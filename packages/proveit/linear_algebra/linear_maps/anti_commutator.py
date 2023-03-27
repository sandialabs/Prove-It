from proveit import Operation, Function, Literal, prover
from proveit import K, V, W
from proveit.logic import SetMembership

class AntiCommutator(Function):
    '''
    The anticommutator of two operators is defined as:
    {A, B} = A ○ B + B ○ A
    '''
    
    _operator_ = Literal(string_format=r'commutator', theory=__file__)

    def __init__(self, A, B, *, styles=None):
        '''
        Denote the commutator of two operators (linear maps)
        '''
        Function.__init__(self, AntiCommutator._operator_, (A, B),
                          styles=styles)

    def string(self, **kwargs):
        # replace with unicode dagger when unicode formats are
        # implemented
        return "{%s, %s'}"%(
                self.operands[0].string(fence=False),
                self.operands[1].string(fence=False))

    def latex(self, **kwargs):
        return r"\left\{%s, %s\right\}"%(
                self.operands[0].string(fence=False),
                self.operands[1].string(fence=False))
