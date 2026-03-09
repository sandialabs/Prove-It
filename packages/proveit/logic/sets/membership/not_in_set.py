from proveit import (Literal, defaults, USE_DEFAULTS, UnusableProof,
                     ProofFailure, equality_prover, prover, relation_prover)
from proveit import x, S
from proveit.relations import Relation
from proveit.classes import ClassMembership


class NotInSet(Relation):
    '''
    Set nonmembership is a special case of class nonmembership, so we'll
    derive from NotInClass for code re-use.  The operators are distinct 
    (though the formatting is the same).
    '''
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in', latex_format=r'\notin',
                         theory=__file__)

    # map (element, domain) pairs to corresponding NotInSet expressions
    notinset_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        Relation.__init__(self, NotInSet._operator_, element, domain,
                          styles=styles)
        element = self.element
        domain = self.domain = self.operands[1]
        NotInSet.notinset_expressions[(element, domain)] = self
        if hasattr(domain, 'nonmembership_object'):
            self.nonmembership_object = self.domain.nonmembership_object(
                element)
            if not isinstance(self.nonmembership_object, SetNonmembership):
                raise TypeError(
                    "The 'nonmembership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.nonmembership_object.__class__,
                     SetNonmembership))

    def __dir__(self):
        '''
        If the domain has a 'nonmembership_object' method,
        include methods from the object it generates (also
        'unfold' which defaults as 'unfold_not_in' if it isn't
        defined in 'nonmembership_object').
        '''
        if 'nonmembership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(list(self.__dict__.keys()) + 'unfold')

    def __getattr__(self, attr):
        '''
        If the domain has a 'nonmembership_object' method,
        include methods from the object it generates (also
        'unfold' defaults as 'unfold_not_in' if it isn't
        defined in 'nonmembership_object').
        '''
        if attr in ('lhs', 'rhs'):
            return Relation.__getattr__(self, attr)
        if 'nonmembership_object' in self.__dict__:
            return getattr(self.nonmembership_object, attr)
        elif attr == 'unfold':
            return self.unfold_not_in  # the default 'unfold' method
        raise AttributeError

    def side_effects(self, judgment):
        '''
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembership_object' method, side effects
        will also be generated from the 'side_effects' object that it
        generates.
        '''
        yield self.unfold_not_in
        if hasattr(self, 'nonmembership_object'):
            for side_effect in self.nonmembership_object.side_effects(
                    judgment):
                yield side_effect

    def negated(self):
        '''
        Return the negated membership expression,
        element not in domain.
        '''
        from .not_in_set import NotInSet
        return NotInSet(self.element, self.domain)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this 'not in' statement is in the set
        of BOOLEANS. For example,
        NotInSet(x, {1, 2, 3}).deduce_in_bool()
        returns |- NotInSet(x, {1, 2, 3}) in Bool
        '''
        from . import not_in_set_is_bool
        from proveit import x, S
        return not_in_set_is_bool.instantiate(
                {x: self.element, S: self.domain})

    @prover
    def unfold_not_in(self, **defaults_config):
        r'''
        From (x \notin y), derive and return Not(x \in y).
        For example,
        NotInSet(a, {b, c, d}).unfold_not_in(
                assumptions=[NotInSet(a, {b, c, d})])
        and
        NotInSet(a, {b, c, d}).unfold_not_in(
                assumptions=[NotEquals(a, b), NotEquals(a, c),
                             NotEquals(a, d)])
        both return
        NotInSet(a, {b, c, d}) |- Not (a in {b, c, d}),
        We include the auto_simplify=False to keep the membership
        result inside the Not() from being reduced to False.
        '''
        from . import unfold_not_in_set
        return unfold_not_in_set.instantiate(
            {x: self.element, S: self.domain}, auto_simplify=False)

    def _readily_provable(self, check_directly_known_elem_equality=True):
        '''
        This membership is readily provable if the membership
        object indicates that it is readily provable or there is a 
        known as-strong membership (with known equal elements and the
        domain a subset of the desired domain).
        '''
        if hasattr(self, 'nonmembership_object'):
            if self.nonmembership_object._readily_provable():
                return True            
        if ClassMembership._readily_provable(
                self, check_directly_known_elem_equality=(
                        check_directly_known_elem_equality)):
            return True
        if self.as_strong_known_nonmembership() is not None:
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
        Attempt to conclude that the element is not in the domain. 
        First see if the corresponding membership has been disproven. 
        Then see if there is a as-strong known nonmembership to use.  
        If not, use the NotInClass conclude strategies (which uses the
        Relation conclude strategies that simplify both sides and then 
        uses the domain-specific conclude method of the membership
        object as a last resort).
        '''
        # Has the membership been disproven?
        if self.negated().disproven(): # don't use readily_disprovable
            return self.conclude_as_folded()
        
        # See if the element, or something known to be equal to
        # the element, is known to be a nonmember of the domain or a 
        # superset of the domain.
        as_strong_nonmembership = self.as_strong_known_nonmembership(
                include_canonical_forms=False)
        if as_strong_nonmembership is not None:
            if as_strong_nonmembership.domain == self.domain:
                try:
                    # Use a known nonmembership from an equivalent member.
                    return self.conclude_from_as_strong_nonmembership(
                            as_strong_nonmembership)
                except UnusableProof:
                    pass

        if hasattr(self, 'nonmembership_object') and (
                self.nonmembership_object._readily_provable()):
            # Don't bother with a fancy, indirect approach if
            # we can readily conclude membership via the membership
            # object.
            return self.nonmembership_object.conclude()

        as_strong_nonmembership = self.as_strong_known_nonmembership(
                include_canonical_forms=True)
        if as_strong_nonmembership is not None:
            # Use a known nonmembership that is at least as strong.
            return self.conclude_from_as_strong_nonmembership(
                    as_strong_nonmembership)

        return Relation.conclude(self)

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from . import fold_not_in_set
        return fold_not_in_set.instantiate(
            {x: self.element, S: self.domain})

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude the negation of nonmembership via
        proving membership.
        '''
        from . import double_negated_membership
        return double_negated_membership.instantiate(
                {x:self.element, S:self.domain})

    @prover
    def conclude_from_as_strong_nonmembership(
            self, as_strong_nonmembership, **defaults_config):
        '''
        Conclude from a nonmembership with an equal element and a 
        domain that is a superset of the desired domain.
        '''
        from proveit.logic import Equals, SubsetEq
        elem_sub = as_strong_nonmembership.element
        if as_strong_nonmembership.domain == self.domain:
            elem_sub_notin_domain = as_strong_nonmembership
        else:
            eq_rel = Equals(as_strong_nonmembership.domain, self.domain)
            if eq_rel.readily_provable():
                # domains are equal -- just substitute the domain.
                elem_sub_notin_domain = eq_rel.sub_right_side_into(
                        as_strong_nonmembership.inner_expr().domain)
            else:
                # S is a subset of R, so now we can prove 
                # x not in S.
                sub_rel = SubsetEq(self.domain, as_strong_nonmembership.domain)
                try:
                    sub_rel.prove()
                except ProofFailure:
                    # May have been blocked to avoid infinite
                    # recursion.
                    return Relation.conclude(self)
                elem_sub_notin_domain = sub_rel.derive_subset_nonmembership(
                        elem_sub)
        if elem_sub == self.element:
            return elem_sub_notin_domain # done
        # Just need to sub in the element for _elem_sub.
        Equals(elem_sub, self.element).conclude_via_transitivity()
        return elem_sub_notin_domain.inner_expr().element.substitute(
                self.element)

    def as_strong_known_nonmembership(self, include_canonical_forms=True):
        '''
        If there is a known nonmembership that is as strong as this 
        one, where the element is equal to this one's element and the 
        domain is a subset of this one's domain, return this
        as-strong known membership.  Otherwise, return None.
        '''
        from proveit.logic import Equals, SubsetEq
        known_nonmemberships = list(
                NotInSet.yield_known_memberships(
                    self.element,
                    include_canonical_forms=include_canonical_forms))
        # First see of there is a known nonmembership with the same domain.
        for known_nonmembership in known_nonmemberships:
            if known_nonmembership.domain == self.domain:
                # this is the best to use; we are done
                return known_nonmembership
        # Next see of there is a known nonmembership with a domain
        # readily provable to be equal to this domain.
        for known_nonmembership in known_nonmemberships:
            eq_rel = Equals(known_nonmembership.domain, self.domain)
            if eq_rel.readily_provable():
                return known_nonmembership
        # Finaly see of there is a known nonmembership with a domain
        # readily provable to be a superset of to this domain.
        for known_nonmembership in known_nonmemberships:
            sub_rel = SubsetEq(self.domain, known_nonmembership.domain)
            if sub_rel.readily_provable():
                return known_nonmembership
        return None # No match found.

class SetNonmembership:
    def __init__(self, element, domain):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        self.element = element
        self.domain = domain
        # The expression represented by this Membership.
        if (element, domain) in NotInSet.notinset_expressions:
            self.expr = NotInSet.notinset_expressions[(element, domain)]
        else:
            self.expr = NotInSet(element, domain)

    def side_effects(self, judgment):
        return # No side-effects by default
        yield

    def _build_canonical_form(self):
        '''
        The canonical form of this nonmembership is based upon
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
        By default, we will determine if this nonmembership is
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
        By default, we will determine if this nonmembership is
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
            "Nonmembership object has no 'conclude' method implemented")

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'definition' method implemented")

    def as_defined(self):
        '''
        Returns the expression that defines the nonmembership.
        '''
        raise NotImplementedError(
            "Nonmembership object, %s, has no 'as_defined' method implemented" 
            % str(self.__class__))

    def readily_in_bool(self, **defaults_config):
        '''
        Unless this is overridden, we won't presume that the membership
        is readily provable to be boolean.
        '''
        return False

    @prover
    def deduce_in_bool(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'deduce_in_bool' method implemented")