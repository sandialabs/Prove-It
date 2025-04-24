from proveit import x, S, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership


class PowerSetMembership(SetMembership):
    '''
    Defines methods that apply to membership in the power set,
    PowerSet(S), of a set S.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return 
            [element in PowerSet(S)] = [SubsetEq(element, S)]
        where self = [element in PowerSet(S)].
        '''
        from . import power_set_def
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return power_set_def.instantiate(
                {x: _x_sub, S: _S_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem in PowerSet(S)], return [SubsetEq(element, S)]
        (i.e., not a Judgment).
        '''
        from proveit.logic import SubsetEq
        element = self.element
        return SubsetEq(element, self.domain.operand)

    @prover
    def unfold(self, **defaults_config):
        '''
        From TRUE or assumed self = [element in PowerSet(S)],
        derive and return [SubsetEq(element, S)].
        '''
        from . import unfold_power_set
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return unfold_power_set.instantiate(
            {x: _x_sub, S: _S_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in PowerSet(S)], and knowing or
        assuming [SubsetEq(elem, S)], derive and
        return self.
        '''
        from . import fold_power_set
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return fold_power_set.instantiate(
            {x: _x_sub, S: _S_sub}, auto_simplify=False)


class PowerSetNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the power set,
    PowerSet(S), of a set S.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for PowerSet nonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self=[elem not in PowerSet(S)], deduce and return
            |- [elem not in PowerSet(S)] = [NotSubsetEq(elem, S)].
        '''
        from . import not_in_power_set_equiv
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return not_in_power_set_equiv.instantiate(
            {x: _x_sub, S: _S_sub}, auto_simplify=False)


    def as_defined(self):
        '''
        From self=[elem not in PowerSet(S)], return
        [NotSubsetEq(elem, S)] (i.e., not as a Judgment).
        '''
        from proveit.logic import NotSubsetEq
        element = self.element
        return NotSubsetEq(element, self.domain.operand)

    @prover
    def unfold(self, **defaults_config):
        '''
        From TRUE or assumed self = [element not in PowerSet(S)],
        derive and return [NotSubsetEq(element, S)].
        '''
        from . import unfold_not_in_power_set
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return unfold_not_in_power_set.instantiate(
            {x: _x_sub, S: _S_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on the self = [elem not in PowerSet(S)], from known
        or assumed [NotSubsetEq(elem, S)], derive and return self.
        '''
        from . import fold_not_in_power_set
        element = self.element
        operand = self.domain.operand
        _x_sub = element
        _S_sub = operand
        return fold_not_in_power_set.instantiate(
            {x: _x_sub, S: _S_sub})
