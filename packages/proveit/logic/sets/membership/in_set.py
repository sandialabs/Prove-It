from proveit import (Literal, defaults, USE_DEFAULTS, ProofFailure,
                     single_or_composite_expression,
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

    def _readily_provable(self):
        '''
        This membership is readily provable if the membership
        object indicates that it is readily provable or there is a 
        known stronger membership (with known equal elements and the
        domain a subset of the desired domain).
        '''
        if InClass._readily_provable(self):
            return True
        if self.stronger_known_membership() is not None:
            return True
        return False

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the element is in the domain.  First
        see if there is a stronger known membership to use.  If not,
        use the InClass conclude strategies (which uses the Relation
        conclude stragegies that simplify both sides and then uses
        the domain-specific conclude method of the membership object
        as a last resort).
        '''
        from proveit.logic import Equals, SubsetEq

        # See if the element, or something known to be equal to
        # the element, is known to be a member of the domain or a subset
        # of the domain.
        stronger_membership = self.stronger_known_membership()
        if stronger_membership is not None:
            elem_sub = stronger_membership.element
            if stronger_membership.domain == self.domain:
                elem_sub_in_domain = stronger_membership
            else:
                eq_rel = Equals(stronger_membership.domain, self.domain)
                if eq_rel.readily_provable():
                    # domains are equal -- just substitute the domain.
                    elem_sub_in_domain = eq_rel.sub_right_side_into(
                            stronger_membership.inner_expr().domain)
                else:
                    # S is a superset of R, so now we can prove x in S.
                    sub_rel = SubsetEq(stronger_membership.domain, self.domain)
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
        return InClass.conclude(self)

    def stronger_known_membership(self):
        '''
        If there is a known membership that is stronger than this one,
        where the element is known to be equal this one's element
        and the domain is a subset of this one's domain, return this
        stronger known membership.  Otherwise, return None.
        '''
        from proveit.logic import Equals, SubsetEq
        for elem_sub in Equals.yield_known_equal_expressions(self.element):
            eq_membership = None # membership in an equal domain
            subset_membership = None # membership in a subset
            for known_membership in InClass.yield_known_memberships(elem_sub):
                eq_rel = Equals(known_membership.domain, self.domain)
                sub_rel = SubsetEq(known_membership.domain, self.domain)
                if known_membership.domain == self.domain:
                    # this is the best to use; we are done
                    return known_membership
                elif eq_rel.readily_provable():
                    eq_membership = known_membership
                elif sub_rel.readily_provable():
                    subset_membership = known_membership
            if eq_membership is not None:
                return eq_membership
            elif subset_membership is not None:
                return subset_membership
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
