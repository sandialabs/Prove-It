from proveit import Literal, defaults, USE_DEFAULTS, equality_prover
from proveit import x, S
from proveit.relation import Relation


class NotInSet(Relation):
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in',
                         latex_format=r'\notin',
                         theory=__file__)

    # maps elements to NotInSet Judgments.
    # For example, map x to (x \nin S) if (x \nin S) is a Judgment.
    known_nonmemberships = dict()

    # map (element, domain) pairs to corresponding NotInSet expressions
    notinset_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        Relation.__init__(self, NotInSet._operator_, element, domain,
                          styles=styles)
        self.element = self.operands[0]
        self.domain = self.operands[1]
        NotInSet.notinset_expressions[(self.element, self.domain)] = self
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
        if attr in ('lhs', 'rhs'):
            return Relation.__getattr__(self, attr)
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
        from proveit.logic import SubsetEq, InSet
        from proveit import ProofFailure
        from proveit.logic import SimplificationError

        # See if the membership is already known.
        if self.element in NotInSet.known_nonmemberships:
            for known_nonmembership in NotInSet.known_nonmemberships[self.element]:
                if known_nonmembership.is_applicable(assumptions):
                    # x not in R is known to be true; if we know that
                    # S subset_eq R, we are done.
                    rel = SubsetEq(self.domain,
                                   known_nonmembership.domain)
                    if rel.proven(assumptions):
                        # S is a subset of R, so now we can prove 
                        # x not in S.
                        return rel.derive_subset_nonmembership(
                            self.element, assumptions)
        # No known membership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(assumptions=assumptions,
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
                simple_elem, self.domain).prove(preserve_all=True)
            inner_expr = simple_nonmembership.inner_expr().element
            return elem_simplification.sub_left_side_into(inner_expr)
        else:
            # If it has a 'nonmembership_object', try to conclude
            # nonmembership using that.
            if hasattr(self, 'nonmembership_object'):
                return self.nonmembership_object.conclude(assumptions=assumptions)
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

    @equality_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Attempt to evaluate whether some x ∉ S is TRUE or FALSE
        using the 'equivalence' method of the domain's 
        'nonmembership_object' if there is one.
        '''
        from proveit.logic import Equals, TRUE, InSet, EvaluationError
        # try an 'definition' method (via the nonmembership object)
        if not hasattr(self, 'membership_object'):
            # Don't know what to do otherwise.
            raise EvaluationError(self)
        definition = self.nonmembership_object.definition()
        rhs_eval = definition.rhs.evaluation()
        evaluation = definition.apply_transitivity(rhs_eval)

        # try also to evaluate this by deducing membership or 
        # non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'nonmembership_object'):
                    self.nonmembership_object.conclude()
            else:
                in_domain = InSet(self.element, self.domain)
                if hasattr(in_domain, 'membership_object'):
                    in_domain.membership_object.conclude()
        except BaseException:
            pass
        return evaluation


class Nonmembership:
    '''
    Base class for any 'nonmembership object' return by a domain's
    'nonmembership_object' method.
    '''

    def __init__(self, element, domain):
        self.element = element
        self.domain = domain
        # The expression represented by this NonMembership.
        if (self.element, self.domain) in NotInSet.notinset_expressions:
            self.expr = NotInSet.notinset_expressions[(self.element, 
                                                       self.domain)]
        else:
            self.expr = NotInSet(self.element, self.domain)

    def side_effects(self, judgment):
        raise NotImplementedError(
            "Nonmembership object has no 'side_effects' method implemented")

    def conclude(self, assumptions):
        raise NotImplementedError(
            "Nonmembership object has no 'conclude' method implemented")

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'definition' method implemented")

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Nonmembership object has no 'deduce_in_bool' method implemented")
