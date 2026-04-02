from proveit import Function, Literal,equality_prover

class Adj(Function):

    _operator_ = Literal(string_format='Adj', theory=__file__)

    def __init__(self, lin_op, *, styles=None):
        '''
        Denote the Hermitan adjoint of a linear operator.
        '''
        Function.__init__(self, Adj._operator_, lin_op,
                          styles=styles)

    def string(self, **kwargs):
        # replace with unicode dagger when unicode formats are
        # implemented
        return self.operand.string(fence=True) + '*'

    def latex(self, **kwargs):
        return self.operand.string(fence=True) + r'^{\dagger}'
    ##### newly added
    @equality_prover('distributed', 'distribute')
    def distribution(self,**defaults_config):
        if hasattr(self.operand, 'adjoint_distribution'):
            return self.operand.adjoint_distribution()
