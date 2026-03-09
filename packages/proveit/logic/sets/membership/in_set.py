from proveit import (Literal, defaults, USE_DEFAULTS, ProofFailure,
                     UnusableProof, single_or_composite_expression,
                     prover, equality_prover, relation_prover)
from proveit.relations import Relation
from proveit.classes import ClassMembership

class InSet(Relation):
    '''
    Set membership is a special case of class membership, so we'll
    derive from InClass for code re-use.  The operators are distinct
    (though the formatting is the same).
    '''
    # operator of the InSet operation
    _operator_ = Literal(string_format='in', latex_format=r'\in',
                         theory=__file__)

    # map (element, domain) pairs to corresponding InSet expressions
    inset_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        Relation.__init__(self, InSet._operator_, element, domain,
                          styles=styles)
        element = self.element
        domain = self.domain = self.operands[1]
        InSet.inset_expressions[(element, domain)] = self
        if hasattr(domain, 'membership_object'):
            self.membership_object = domain.membership_object(element)
            if not isinstance(self.membership_object, SetMembership):
                raise TypeError(
                    "The 'membership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.membership_object.__class__, 
                     SetMembership))

    def __dir__(self):
        '''
        If the domain has a 'membership_object' method, include
        methods from the object it generates.
        '''
        if 'membership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(self.__dict__.keys())

    def __getattr__(self, attr):
        '''
        If the domain has a 'membership_object' method, include
        methods from the object it generates.
        '''
        if attr in ('lhs', 'rhs'):
            return Relation.__getattr__(self, attr)
        if 'membership_object' in self.__dict__:
            return getattr(self.membership_object, attr)
        raise AttributeError

    @staticmethod
    def reversed_operator_str(formatType):
        r'''
        Reversing \in gives \ni.  Reversing "in" gives "contains".
        '''
        if formatType=='latex':
            return r'\ni'
        else:
            return 'contains'

    def side_effects(self, judgment):
        '''
        If the domain has a 'membership_object' method, side effects
        will also be generated from the 'side_effects' object that it
        generates.
        '''
        if hasattr(self, 'membership_object'):
            for side_effect in self.membership_object.side_effects(
                    judgment):
                yield side_effect

    def negated(self):
        '''
        Return the negated membership expression,
        element not in domain.
        '''
        from .not_in_set import NotInSet
        return NotInSet(self.element, self.domain)

    def _readily_provable(self, check_directly_known_elem_equality=True):
        '''
        This membership is readily provable if the membership
        object indicates that it is readily provable or there is a 
        known as-strong membership (with known equal elements and the
        domain a subset of the desired domain).
        '''
        if hasattr(self, 'membership_object'):
            if self.membership_object._readily_provable():
                return True            
        if ClassMembership._readily_provable(
                self, check_directly_known_elem_equality=(
                        check_directly_known_elem_equality)):
            return True
        if self.as_strong_known_membership() is not None:
            return True
        return False

    def _readily_disprovable(self):
        '''
        This membership is readily disprovable if the corresponding
        nonmembership is readily provable.
        '''
        return self.negated().readily_provable()
    
    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the element is in the domain.  First
        see if there is an equivalent known membership to use
        (same domain).  If not, see if there is a membership object
        that is readily provable and conclude via that object if so.
        Then check for a membership that is at least as strong with
        a possibly different domain to use.  Finally, defer to
        InClass.conclude which defers to InRelation.conclude and
        attempts simplifications.
        '''
        # See if the element, or something known to be equal to
        # the element, is known to be a member of the domain or a subset
        # of the domain.
        as_strong_membership = self.as_strong_known_membership(
                include_canonical_forms=False)
        if as_strong_membership is not None:
            if as_strong_membership.domain == self.domain:
                try:
                    # Use a known membership from an equivalent member.
                    return self.conclude_from_as_strong_membership(
                            as_strong_membership)
                except UnusableProof:
                    pass
        
        if hasattr(self, 'membership_object') and (
                self.membership_object._readily_provable()):
            # Don't bother with a fancy, indirect approach if
            # we can readily conclude membership via the membership
            # object.
            return self.membership_object.conclude()

        as_strong_membership = self.as_strong_known_membership(
                include_canonical_forms=True)
        if as_strong_membership is not None:
            # Use a known membership that is at least as strong.
            return self.conclude_from_as_strong_membership(
                    as_strong_membership)

        return Relation.conclude(self)
    
    @prover
    def conclude_from_as_strong_membership(self, as_strong_membership,
                                           **defaults_config):
        '''
        Conclude from a membership with an equal element and a domain
        that is a subset of the desired domain.
        '''
        from proveit.logic import Equals, SubsetEq
        elem_sub = as_strong_membership.element
        if as_strong_membership.domain == self.domain:
            elem_sub_in_domain = as_strong_membership
        else:
            eq_rel = Equals(as_strong_membership.domain, self.domain)
            if eq_rel.readily_provable():
                # domains are equal -- just substitute the domain.
                elem_sub_in_domain = eq_rel.sub_right_side_into(
                        as_strong_membership.inner_expr().domain)
            else:
                # S is a superset of R, so now we can prove x in S.
                sub_rel = SubsetEq(as_strong_membership.domain, self.domain)
                try:
                    sub_rel.prove()
                except ProofFailure:
                    # May have been blocked to avoid infinite
                    # recursion.
                    return Relation.conclude(self)
                elem_sub_in_domain = sub_rel.derive_superset_membership(
                        elem_sub)
        if elem_sub == self.element:
            return elem_sub_in_domain # done
        # Just need to sub in the element for _elem_sub.
        return elem_sub_in_domain.inner_expr().element.substitute(
                self.element)        

    def as_strong_known_membership(self, include_canonical_forms=True):
        '''
        If there is a known membership that is as strong as this one,
        where the element is known to be equal this one's element
        and the domain is a subset of this one's domain, return this
        as-strong known membership.  Otherwise, return None.
        '''
        from proveit.logic import Equals, SubsetEq
        known_memberships = list(
                InSet.yield_known_memberships(
                    self.element,
                    include_canonical_forms=include_canonical_forms))
        # First see of there is a known membership with the same domain.
        for known_membership in known_memberships:
            if known_membership.domain == self.domain:
                # this is the best to use; we are done
                return known_membership
        # Next see of there is a known membership with a domain
        # readily provable to be equal to this domain.
        for known_membership in known_memberships:
            eq_rel = Equals(known_membership.domain, self.domain)
            if eq_rel.readily_provable():
                return known_membership
        # Finally see of there is a known membership with a domain
        # readily provable to be a subset of to this domain.
        for known_membership in known_memberships:
            sub_rel = SubsetEq(known_membership.domain, self.domain)
            if sub_rel.readily_provable():
                return known_membership
        return None # No match found.

class SetMembership:
    def __init__(self, element, domain):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        self.element = element
        self.domain = domain
        # The expression represented by this Membership.
        if (element, domain) in InSet.inset_expressions:
            self.expr = InSet.inset_expressions[(element, domain)]
        else:
            self.expr = InSet(element, domain)

    def side_effects(self, judgment):
        return # No side-effects by default
        yield

    def _build_canonical_form(self):
        '''
        The canonical form of this membership is based upon
        'as_defined' which defines what the membership means.
        '''
        try:
            return self.as_defined().canonical_form()
        except NotImplementedError:
            # If 'as_defined' is not implemented, use the default
            # method of building the canonical form.
            return Relation._build_canonical_form(self.expr)

    def _readily_provable(self):
        '''
        By default, we will determine if this membership is
        readily provable if its "as_defined()" expression is
        readily provable.
        '''
        try:
            return self.as_defined().readily_provable()
        except NotImplementedError:
            # If 'as_defined' is not implemented, this default
            # method for determining provability can never be true.
            return False

    def _readily_disprovable(self):
        '''
        By default, we will determine if this membership is
        readily disprovable if its "as_defined()" expression is
        readily disprovable.
        '''
        try:
            return self.as_defined().readily_disprovable()
        except NotImplementedError:
            # If 'as_defined' is not implemented, this default
            # method for determining provability can never be true.
            return False

    @prover
    def conclude(self, **defaults_config):
        raise NotImplementedError(
            "Membership object, %s, has no 'conclude' method implemented" % str(
                self.__class__))

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove the membership equal to an expression that defines the
        membership.
        '''
        raise NotImplementedError(
            "Membership object, %s, has no 'definition' method implemented" % str(
                self.__class__))
    
    def as_defined(self):
        '''
        Returns the expression that defines the membership.
        '''
        raise NotImplementedError(
            "Membership object, %s, has no 'as_defined' method implemented" % str(
                self.__class__))

    def _deduce_canonically_equal(self, rhs):
        '''
        Equate 'self' to the 'rhs' via the definition.  Raises 
        NotImplementedError if 'definition' is not implemented.
        '''
        definition = self.definition()
        def_eq_rhs = definition.deduce_canonically_equal(rhs)
        return definition.apply_transitivity(def_eq_rhs)
        
    def readily_in_bool(self, **defaults_config):
        '''
        Unless this is overridden, we won't presume that the membership
        is readily provable to be boolean.
        '''
        return False

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        raise NotImplementedError(
            "Membership object, %s, has no 'deduce_in_bool' method implemented" % str(
                self.__class__))