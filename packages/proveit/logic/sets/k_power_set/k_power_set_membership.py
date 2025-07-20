from proveit import k, A, S, equality_prover, prover
from proveit.logic import (
        And, Equals, NotEquals, Or, SetMembership, SetNonmembership)
from proveit.logic.sets import Card, NotSubsetEq, SubsetEq


class KPowerSetMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of
    k-element subsets of a set.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return 
        [elem in KPowerSet(S, k)] = [SubsetEq(elem, S) AND |elem|=k]
        where self = [element in KPowerSet(S)].
        '''
        from . import k_power_set_def
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return k_power_set_def.instantiate(
                {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem in KPowerSet(S, k)], return
        [SubsetEq(elem, S) AND |elem|=k] (i.e. not a Judgment).
        '''
        element = self.element
        superset = self.domain.operands[0]
        subset_size = self.domain.operands[1]
        return And(SubsetEq(element, superset),
                   Equals(Card(element), subset_size))

    @prover
    def unfold(self, **defaults_config):
        '''
        From TRUE or assumed self = [elem in KPowerSet(S, k)],
        derive and return [SubsetEq(elem, S) AND |elem| = k].
        '''
        from . import unfold_k_power_set
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return unfold_k_power_set.instantiate(
            {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in KPowerSet(S, k)], and knowing or
        assuming [SubsetEq(elem, S) AND |elem| =k], derive and
        return self.
        '''
        from . import fold_k_power_set
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return fold_k_power_set.instantiate(
            {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)


class KPowerSetNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set of
    k-element subsets of a set.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for KPowerSet nonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self=[elem not in KPowerSet(S, k)], deduce and return
            |- [elem not in KPowerSet(S, k)] =
               [NotSubsetEq(elem, S) OR |elem| != k].
        '''
        from . import not_in_k_power_set_equiv
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return not_in_k_power_set_equiv.instantiate(
            {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem not in KPowerSet(S, k)], return
        [NotSubsetEq(elem, S) OR |elem| != k] (i.e., not a Judgment).
        '''
        element = self.element
        superset = self.domain.operands[0]
        subset_size = self.domain.operands[1]
        return Or(NotSubsetEq(element, superset),
                   NotEquals(Card(element), subset_size))

    @prover
    def unfold(self, **defaults_config):
        '''
        From TRUE or assumed self = [elem not in KPowerSet(S, k)],
        derive and return [NotSubsetEq(elem, S) OR |elem| != k].
        '''
        from . import unfold_not_in_k_power_set
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return unfold_not_in_k_power_set.instantiate(
            {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on the self = [elem not in KPowerSet(S, k)], from known
        or assumed [NotSubsetEq(elem, S) OR |elem| != k], derive and 
        return self.
        '''
        from . import fold_not_in_k_power_set
        element = self.element
        operands = self.domain.operands
        _A_sub = element
        _S_sub = operands[0]
        _k_sub = operands[1]
        return fold_not_in_k_power_set.instantiate(
            {A:_A_sub, S: _S_sub, k:_k_sub}, auto_simplify=False)

