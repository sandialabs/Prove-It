from proveit import Theory, Function, Literal, USE_DEFAULTS
from proveit.logic import Equals
from proveit.numbers import one

class GCD(Function):

    _operator_ = Literal('gcd', theory=__file__)
    
    def __init__(self, a, b):
        Function.__init__(self, GCD._operator_, [a, b])

    def deduce_relatively_prime(self, assumptions=USE_DEFAULTS):
        '''
        From GCD(a,b) expression and knowledge or assumption that
        GCD(a,b)=1, deduce that a, b are relatively prime and return
        the universally-quantified claim that for all natural positive
        numbers p > 1 we have Not(p|a AND p|b).
        '''
        from ._theorems_ import GCD_one_def
        _a, _b = GCD_one_def.instanceParams
        return GCD_one_def.instantiate(
        	{_a:self.operands[0], _b:self.operands[1]},
        	assumptions=assumptions)
