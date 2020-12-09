from proveit.basiclogic import *
from proveit.numberss import *

QubitRegisterSpace = lambda n : TensorExp(Exp(Complex, two), n)
RegisterSU = lambda n : SU(Exp(two, n))
