from proveit.basiclogic import *
from proveit.numberss import *


def QubitRegisterSpace(n): return TensorExp(Exp(Complex, two), n)
def RegisterSU(n): return SU(Exp(two, n))
