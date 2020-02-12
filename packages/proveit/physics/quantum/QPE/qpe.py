from proveit.basiclogic import *
from proveit.numbers import *

QubitRegisterSpace = lambda n : TensorExp(Exp(Complexes, two), n)
RegisterSU = lambda n : SU(Exp(two, n))
