from proveit import (equality_prover, Operation, Function, Literal, 
                     TransRelUpdater)
from proveit import x
from proveit.linear_algebra import SU, TensorExp
from proveit.numbers import one, num, Complex, Exp

pkg = __package__  # delete this later; will no longer be needed




class Meas(Function):
    '''
    Class to represent the making of a measurement on a ket |𝜑⟩.
    '''
    # the literal operator of the Meas operation
    _operator_ = Literal(string_format='MEAS', latex_format=r'\mathcal{M}',
                         theory=__file__)

    def __init__(self, ket, *, styles=None):
        Function.__init__(self, Meas._operator_, ket, styles=styles)
        self.ket = ket


def QubitRegisterSpace(num_Qbits):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    # need some extra curly brackets around the Exp() expression
    # to allow the latex superscript to work on something
    # already superscripted
    return TensorExp({Exp(Complex, num(2))}, num_Qbits)


def RegisterSU(n):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    return SU(Exp(num(2), n))
