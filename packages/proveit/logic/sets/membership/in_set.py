from proveit import Literal, Operation, defaults, USE_DEFAULTS


class InSet(Operation):
    # operator of the InSet operation
    _operator_ = Literal(string_format='in',
                         latex_format=r'\in',
                         theory=__file__)

    # maps elements to InSet Judgments.
    # For example, map x to (x in S) if (x in S) is a Judgment.
    known_memberships = dict()

    def __init__(self, element, domain, *, styles=None):
        Operation.__init__(self, InSet._operator_, (element, domain),
                           styles=styles)
        self.element = self.operands[0]
        self.domain = self.operands[1]
        if hasattr(self.domain, 'membership_object'):
            self.membership_object = self.domain.membership_object(element)
            if not isinstance(self.membership_object, Membership):
                raise TypeError(
                    "The 'membership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.membership_object.__class__, Membership))

    def __dir__(self):
        '''
        If the domain has a 'membership_object' method, include methods from the
        object it generates.
        '''
        if 'membership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(self.__dict__.keys())

    def __getattr__(self, attr):
        '''
        If the domain has a 'membership_object' method, include methods from the
        object it generates.
        '''
        if 'membership_object' in self.__dict__:
            return getattr(self.membership_object, attr)
        raise AttributeError

    def side_effects(self, judgment):
        '''
        Store the proven membership in known_memberships.
        If the domain has a 'membership_object' method, side effects
        will also be generated from the 'side_effects' object that it generates.
        '''
        InSet.known_memberships.setdefault(self.element, set()).add(judgment)
        if hasattr(self, 'membership_object'):
            for side_effect in self.membership_object.side_effects(judgment):
                yield side_effect

    def negation_side_effects(self, judgment):
        '''
        Fold Not(x in S) as (x not-in S) as an automatic side-effect.
        '''
        yield self.deduce_not_in

    def deduce_not_in(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from .not_in_set import NotInSet
        yield NotInSet(self.element, self.domain).conclude_as_folded(assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this membership statement is in the
        Boolean set (i.e. membership is True or False).
        '''
        if hasattr(self, 'membership_object'):
            return self.membership_object.deduce_in_bool(assumptions)
        raise AttributeError

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is in the domain.
        First, see if it is known to be contained in a known subset of the
        domain.  Next, check if the element has a known simplification; if so,
        try to derive membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.membership_object.conclude(..)' method to prove
        the membership.  If that fails, try simplifying the element
        again, this time using automation to push the simplification through
        if possible.
        '''
        from proveit.logic import Equals, SubsetEq
        from proveit import ProofFailure
        from proveit.logic import SimplificationError

        # See if the element, or something known to be equal to
        # the element, is known to be a member of the domain or a subset
        # of the domain.
        for elem_sub in Equals.yield_known_equal_expressions(
                self.element, assumptions=assumptions):
            same_membership = None # membership in self.domain
            eq_membership = None # membership in an equal domain
            subset_membership = None # membership in a subset
            for known_membership in InSet.yield_known_memberships(
                    elem_sub, assumptions):
                eq_rel = Equals(known_membership.domain, self.domain)
                sub_rel = SubsetEq(known_membership.domain, self.domain)
                if known_membership.domain == self.domain:
                    same_membership = known_membership
                    break # this is the best to use; we are done
                elif eq_rel.proven(assumptions):
                    eq_membership = known_membership
                elif sub_rel.proven(assumptions):
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
                        elem_sub, assumptions)
            if elem_sub_in_domain is not None:
                # We found what we are looking for.
                if elem_sub == self.element:
                    return elem_sub_in_domain # done
                # Just need to sub in the element for _elem_sub.
                Equals(elem_sub, self.element).conclude_via_transitivity(
                        assumptions)
                return elem_sub_in_domain.inner_expr().element.substitute(
                        self.element, assumptions=assumptions)

        # No known membership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(assumptions=assumptions,
                                                              automation=False)
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None  # reflection doesn't count
        except SimplificationError:
            elem_simplification = None

        if elem_simplification is None:
            # Let's try harder to simplify the element.
            try:
                elem_simplification = self.element.simplification(assumptions=assumptions)
                if elem_simplification.lhs == elem_simplification.rhs:
                    elem_simplification = None  # reflection doesn't count
            except SimplificationError:
                pass

        # If the element simplification succeeded, prove the membership
        # via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_membership = InSet(
                simple_elem, self.domain).prove(assumptions)
            inner_expr = simple_membership.inner_expr().element
            return elem_simplification.sub_left_side_into(
                inner_expr, assumptions)
        else:
            # Unable to simplify the element.  Try to conclude via
            # the 'membership_object' if there is one.
            if hasattr(self, 'membership_object'):
                return self.membership_object.conclude(assumptions=assumptions)

            raise ProofFailure(self, assumptions,
                               "Unable to conclude automatically; "
                               "the domain, %s, has no 'membership_object' "
                               "method with a strategy for proving "
                               "membership." % self.domain)
    
    @staticmethod
    def yield_known_memberships(element, assumptions=USE_DEFAULTS):
        '''
        Yield the known memberships of the given element applicable
        under the given assumptions.
        '''
        assumptions = defaults.checked_assumptions(assumptions)       
        if element in InSet.known_memberships:
            for known_membership in InSet.known_memberships[element]:
                if known_membership.is_sufficient(assumptions):
                    yield known_membership

    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Attempt to form evaluation of whether (element in domain) is
        TRUE or FALSE.  If the domain has a 'membership_object' method,
        attempt to use the 'equivalence' method from the object it generates.
        '''
        from proveit.logic import TRUE, NotInSet
        # try an 'equivalence' method (via the membership object)
        equiv = self.membership_object.equivalence(assumptions)
        rhs_eval = equiv.rhs.evaluation(assumptions=assumptions)
        evaluation = equiv.apply_transitivity(
            rhs_eval, assumptions=assumptions)
        # try also to evaluate this by deducing membership
        # or non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'membership_object'):
                    self.membership_object.conclude(assumptions=assumptions)
            else:
                not_in_domain = NotInSet(self.element, self.domain)
                if hasattr(not_in_domain, 'nonmembership_object'):
                    not_in_domain.nonmembership_object.conclude(
                        assumptions=assumptions)
        except BaseException:
            pass
        return evaluation


class Membership:
    def __init__(self, element):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        self.element = element

    def side_effects(self, judgment):
        raise NotImplementedError(
            "Membership object, %s, has no 'side_effects' method implemented" % str(
                self.__class__))

    def conclude(self, assumptions):
        raise NotImplementedError(
            "Membership object, %s, has no 'conclude' method implemented" % str(
                self.__class__))

    def equivalence(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Membership object, %s, has no 'equivalence' method implemented" % str(
                self.__class__))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Membership object, %s, has no 'deduce_in_bool' method implemented" % str(
                self.__class__))
