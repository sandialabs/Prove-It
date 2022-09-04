from proveit import (Literal, defaults, USE_DEFAULTS, ProofFailure,
                     UnusableProof, single_or_composite_expression,
                     prover, equality_prover, relation_prover)
from proveit.relation import Relation
from proveit.logic.classes import InClass, ClassMembership

class InSet(InClass):
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
        element = single_or_composite_expression(element)
        domain = single_or_composite_expression(domain)
        InSet.inset_expressions[(element, domain)] = self
        InClass.__init__(self, element, domain, operator=InSet._operator_,
                         styles=styles)

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
        if InClass._readily_provable(
                self, check_directly_known_elem_equality=(
                        check_directly_known_elem_equality)):
            return True
        if self.as_strong_known_membership() is not None:
            return True
        return False

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
        as_strong_membership = self.as_strong_known_membership()
        if as_strong_membership is not None:
            if as_strong_membership.domain == self.domain:
                try:
                    # Use an equivalent known membership.
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

        if as_strong_membership is not None:
            # Use a known membership that is at least as strong.
            return self.conclude_from_as_strong_membership(
                    as_strong_membership)

        return InClass.conclude(self)
    
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
                    return InClass.conclude(self)
                elem_sub_in_domain = sub_rel.derive_superset_membership(
                        elem_sub)
        if elem_sub == self.element:
            return elem_sub_in_domain # done
        # Just need to sub in the element for _elem_sub.
        return elem_sub_in_domain.inner_expr().element.substitute(
                self.element)        

    def as_strong_known_membership(self):
        '''
        If there is a known membership that is as strong as this one,
        where the element is known to be equal this one's element
        and the domain is a subset of this one's domain, return this
        as-strong known membership.  Otherwise, return None.
        '''
        from proveit.logic import Equals, SubsetEq
        known_memberships = list(
                InClass.yield_known_memberships(self.element))
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
        # Finaly see of there is a known membership with a domain
        # readily provable to be a subset of to this domain.
        for known_membership in known_memberships:
            sub_rel = SubsetEq(known_membership.domain, self.domain)
            if sub_rel.readily_provable():
                return known_membership
        return None # No match found.

class SetMembership(ClassMembership):
    def __init__(self, element, domain):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        # The expression represented by this Membership.
        if (element, domain) in InSet.inset_expressions:
            expr = InSet.inset_expressions[(element, domain)]
        else:
            expr = InSet(element, domain)
        ClassMembership.__init__(self, element, domain, expr=expr)
