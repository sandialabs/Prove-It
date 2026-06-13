from proveit import x, prover
from proveit.logic import SetMembership, SetNonmembership

class EmptySetMembership(SetMembership):
    '''
    Defines methods that apply to membership in the empty set
    (EmptySet). Technically, nothing is a member of the empty set;
    thus deductions to the contrary allow us to disprove assumptions
    that lead to such a deduction, and an empty set membership
    assumption should allow us to conclude anything.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    # def side_effects(self, judgment):
    #     '''
    #     Unfold the enumerated set membership as a side-effect.
    #     '''
    #     yield self.unfold

    # @equality_prover('defined', 'define')
    # def definition(self, **defaults_config):
    #     '''
    #     Deduce and return 
    #         [element in (A union B ...)] = 
    #         [(element in A) or (element in B) ...]
    #     where self = (A union B ...).
    #     '''
    #     from . import union_def
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return union_def.instantiate(
    #             {m: _m, x: element, A: _A}, auto_simplify=False)

    # def as_defined(self):
    #     '''
    #     From self=[elem in (A U B U ...)], return
    #     [(element in A) or (element in B) or ...].
    #     '''
    #     from proveit.logic import Or, InSet
    #     element = self.element
    #     return Or(*self.domain.operands.map_elements(
    #             lambda subset : InSet(element, subset)))

    # @prover
    # def unfold(self, **defaults_config):
    #     '''
    #     From [element in (A union B ...)], derive and return
    #     [(element in A) or (element in B) ...],
    #     where self represents [element in (A union B ...)].
    #     '''
    #     from . import membership_unfolding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_unfolding.instantiate(
    #         {m: _m, x: element, A: _A}, auto_simplify=False)

    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     Called on self = [elem in (A U B U ...)], and knowing or
    #     assuming [[elem in A] OR [elem in B] OR ...], derive and
    #     return self.
    #     '''
    #     from . import membership_folding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_folding.instantiate({m: _m, x: element, A: _A})

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From self = [x in EmptySet], derive and return FALSE.
        '''
        from . import empty_set_contradiction
        _x_sub = self.element
        return empty_set_contradiction.instantiate({x: _x_sub})

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''
        From self = x in EmptySet, derive the negated conclusion,
        provided that the conclusion implies x in EmptySet (because
        x in EmptySet should never be true).
        '''
        print(f"Entering EmptySetMembership.deny_via_contradiction() with:")
        print(f"    self = {self}")
        display(self)
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self.expr, conclusion)

    def readily_in_bool(self):
        return True # EmptySetMembership is always boolean

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import empty_set_membership_is_bool
        _x_sub = self.element
        return empty_set_membership_is_bool.instantiate({x: _x_sub})


class EmptySetNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the empty set
    (EmptySet).
    UNDER CONSTRUCTION
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)
        self.domain = domain

    # def _readily_provable(self):
    #     '''
    #     The Nonmembership is readily provabile if the element
    #     is readily known to be a non-integer or its readily known to be 
    #     below/above the lower/upper bound.
    #     '''
    #     _a = self.domain.lower_bound
    #     _b = self.domain.upper_bound
    #     _x = self.element
    #     return InSet(_x, Integer).readily_disprovable() or (
    #             Less(_x, _a).readily_provable() or
    #             Less(_b, _x).readily_provable())

    # def side_effects(self, judgment):
    #     '''
    #     Yield some possible side effects of Interval set nonmembership:
    #     (1) if element is an integer, deduce some possible bounds on it;
    #     '''
    #     if InSet(self.element, Integer).readily_provable():
    #         yield self.deduce_int_element_bounds

    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     From x not in Integers, or an integer x such that x < a or x > b,
    #     derive and return [element x not in Interval(a, b)],
    #     where self is the IntervalNonmembership object.
    #     '''
    #     _a = self.domain.lower_bound
    #     _b = self.domain.upper_bound
    #     _x = self.element
    #     if InSet(self.element, Integer).readily_provable():
    #         from . import int_not_in_interval
    #         return int_not_in_interval.instantiate(
    #                 {a: _a, b: _b, x: _x})
    #     else:
    #         from . import not_int_not_in_interval
    #         return not_int_not_in_interval.instantiate(
    #                 {a: _a, b: _b, x: _x})

    def readily_in_bool(self):
        return True # EmptySetNonmembership is always boolean

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import empty_set_nonmembership_is_bool
        _x_sub = self.element
        return empty_set_nonmembership_is_bool.instantiate({x: _x_sub})
