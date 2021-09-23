from proveit import (Literal, defaults, USE_DEFAULTS,
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
        InSet.inset_expressions[(element, domain)] = self
        InClass.__init__(self, element, domain, operator=InSet._operator_,
                         styles=styles)

    def negated(self):
        '''
        Return the negated membership expression,
        element not in domain.
        '''
        from not_in_set import NotInSet
        return NotInSet(self.element, self.domain)

    @prover
    def deduce_not_in(self, **defaults_config):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from .not_in_set import NotInSet
        return NotInSet(self.element, self.domain).conclude_as_folded()

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the element is in the domain.  First,
        see if it is known to be contained in a known subset of the
        domain.  Next, check if the element has a known simplification;
        if so, try to derive membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.membership_object.conclude(..)' method to prove
        the membership.  If that fails, try simplifying the element
        again, this time using automation to push the simplification
        through if possible.
        '''
        from proveit.logic import Equals, SubsetEq
        from proveit import ProofFailure, UnsatisfiedPrerequisites
        from proveit.logic import SimplificationError

        # See if the element, or something known to be equal to
        # the element, is known to be a member of the domain or a subset
        # of the domain.
        for elem_sub in Equals.yield_known_equal_expressions(self.element):
            same_membership = None # membership in self.domain
            eq_membership = None # membership in an equal domain
            subset_membership = None # membership in a subset
            for known_membership in InSet.yield_known_memberships(elem_sub):
                eq_rel = Equals(known_membership.domain, self.domain)
                sub_rel = SubsetEq(known_membership.domain, self.domain)
                if known_membership.domain == self.domain:
                    same_membership = known_membership
                    break # this is the best to use; we are done
                elif eq_rel.proven():
                    eq_membership = known_membership
                elif sub_rel.proven():
                    subset_membership = known_membership
            elem_sub_in_domain = None
            if same_membership is not None:
                elem_sub_in_domain = same_membership
            elif eq_membership is not None:
                # domains are equal -- just substitute to domain.
                eq_rel = Equals(eq_membership.domain, self.domain)
                elem_sub_in_domain = eq_rel.sub_right_side_into(
                    eq_membership.inner_expr().domain)
            elif subset_membership is not None:
                # S is a superset of R, so now we can prove x in S.
                sub_rel = SubsetEq(subset_membership.domain, self.domain)
                elem_sub_in_domain = sub_rel.derive_superset_membership(
                        elem_sub)
            if elem_sub_in_domain is not None:
                # We found what we are looking for.
                if elem_sub == self.element:
                    return elem_sub_in_domain # done
                # Just need to sub in the element for _elem_sub.
                Equals(elem_sub, self.element).conclude_via_transitivity()
                return elem_sub_in_domain.inner_expr().element.substitute(
                        self.element)

        # No known membership works.  Let's try to work with a
        # simplification of the element instead.
        elem_simplification = None
        try:
            elem_simplification = self.element.simplification()
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None  # reflection doesn't count
        except (SimplificationError, ProofFailure, NotImplementedError,
                UnsatisfiedPrerequisites):
            pass

        # If the element simplification succeeded, prove the membership
        # via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_membership = InSet(
                simple_elem, self.domain).prove()
            inner_expr = simple_membership.inner_expr().element
            return elem_simplification.sub_left_side_into(inner_expr)
        else:
            # Unable to simplify the element.  Try to conclude via
            # the 'membership_object' if there is one.
            if hasattr(self, 'membership_object'):
                return self.membership_object.conclude()

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
