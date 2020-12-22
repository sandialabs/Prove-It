from proveit import Literal, Operation, USE_DEFAULTS
from proveit import x, S


class NotInSet(Operation):
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in',
                         latex_format=r'\notin',
                         theory=__file__)

    # maps elements to NotInSet Judgments.
    # For example, map x to (x \nin S) if (x \nin S) is a Judgment.
    known_nonmemberships = dict()

    def __init__(self, element, domain):
        Operation.__init__(self, NotInSet._operator_, (element, domain))
        self.element = self.operands[0]
        self.domain = self.operands[1]
        if hasattr(self.domain, 'nonmembership_object'):
            self.nonmembership_object = self.domain.nonmembership_object(
                element)
            if not isinstance(self.nonmembership_object, Nonmembership):
                raise TypeError(
                    "The 'nonmembership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.nonmembership_object.__class__, Nonmembership))

    def __dir__(self):
        '''
        If the domain has a 'nonmembership_object' method, include methods from the
        object it generates (also 'unfold' which defaults as 'unfold_not_in' if it
        isn't defined in 'nonmembership_object').
        '''
        if 'nonmembership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(list(self.__dict__.keys()) + 'unfold')

    def __getattr__(self, attr):
        '''
        If the domain has a 'nonmembership_object' method, include methods from the
        object it generates (also 'unfold' defaults as 'unfold_not_in' if it isn't
        defined in 'nonmembership_object').
        '''
        if 'nonmembership_object' in self.__dict__:
            return getattr(self.nonmembership_object, attr)
        elif attr == 'unfold':
            return self.unfold_not_in  # the default 'unfold' method
        raise AttributeError

    def side_effects(self, judgment):
        '''
        Store the proven non-membership in known_nonmemberships.
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembership_object' method, side effects
        will also be generated from the 'side_effects' object that it generates.
        '''
        NotInSet.known_nonmemberships.setdefault(
            self.element, set()).add(judgment)
        yield self.unfold_not_in
        if hasattr(self, 'nonmembership_object'):
            for side_effect in self.nonmembership_object.side_effects(
                    judgment):
                yield side_effect

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        '''
        from . import not_in_set_is_bool
        from proveit import x, S
        return not_in_set_is_bool.instantiate(
            {x: self.element, S: self.domain}, assumptions=assumptions)

    def unfold_not_in(self, assumptions=USE_DEFAULTS):
        r'''
        From (x \notin y), derive and return Not(x \in y).
        '''
        from . import unfold_not_in_set
        return unfold_not_in_set.instantiate(
            {x: self.element, S: self.domain}, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is in the domain.
        First, see if it is not contained in a superset of the domain.
        Next, check if the element has a known simplification; if so,
        try to derive non-membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.nonmembership_object.conclude(..)' method to prove
        the non-membership.  If that fails, try simplifying the element
        again, this time using automation to push the simplification through
        if possible.
        As a last resort, try 'conclude_as_folded'.
        '''
        from proveit.logic import SupersetEq, InSet
        from proveit import ProofFailure
        from proveit.logic import SimplificationError

        # See if the membership is already known.
        if self.element in NotInSet.known_nonmemberships:
            for known_nonmembership in NotInSet.known_nonmemberships[self.element]:
                if known_nonmembership.is_sufficient(assumptions):
                    # x not in R is a judgment; if we know that
                    # R supseteq S, we are done.
                    sup_rel = SupersetEq(known_nonmembership.domain,
                                         self.domain)
                    if sup_rel.proven(assumptions):
                        # S is a subset of R, so now we can prove x not in S.
                        return sup_rel.derive_subset_non_membership(
                            self.element, assumptions)
        # No known membership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(assumptions,
                                                              automation=True)
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None  # reflection doesn't count
        except SimplificationError:
            elem_simplification = None

        # If the element simplification succeeded, prove the membership
        # via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_nonmembership = NotInSet(
                simple_elem, self.domain).prove(assumptions)
            inner_expr = simple_nonmembership.inner_expr().element
            return elem_simplification.sub_left_side_into(
                inner_expr, assumptions)
        else:
            # If it has a 'nonmembership_object', try to conclude
            # nonmembership using that.
            if hasattr(self, 'nonmembership_object'):
                return self.nonmembership_object.conclude(assumptions)
            else:
                # Otherwise, attempt to conclude via Not(x in S)
                return self.conclude_as_folded(assumptions=assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from . import fold_not_in_set
        return fold_not_in_set.instantiate(
            {x: self.element, S: self.domain}, assumptions=assumptions)

    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Attempt to form evaluation of whether (element not in domain) is
        TRUE or FALSE.  If the domain has a 'membership_object' method,
        attempt to use the 'equivalence' method from the object it generates.
        '''
        from proveit.logic import Equals, TRUE, InSet
        # try an 'equivalence' method (via the nonmembership object)
        equiv = self.nonmembership_object.equivalence(assumptions)
        val = equiv.evaluation(assumptions).rhs
        evaluation = Equals(equiv, val).prove(assumptions=assumptions)
        # try also to evaluate this by deducing membership or non-membership
        # in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'nonmembership_object'):
                    self.nonmembership_object.conclude(assumptions=assumptions)
            else:
                in_domain = In(self.element, self.domain)
                if hasattr(in_domain, 'membership_object'):
                    in_domain.membership_object.conclude(
                        assumptions=assumptions)
        except BaseException:
            pass
        return evaluation


class Nonmembership:
    '''
    Base class for any 'nonmembership object' return by a domain's
    'nonmembership_object' method.
    '''

    def __init__(self, element):
        self.element = element

    def side_effects(self, judgment):
        raise NotImplementedError(
            "Nonmembership object has no 'side_effects' method implemented")

    def conclude(self, assumptions):
        raise NotImplementedError(
            "Nonmembership object has no 'conclude' method implemented")

    def equivalence(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Nonmembership object has no 'equivalence' method implemented")

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Nonmembership object has no 'deduce_in_bool' method implemented")
