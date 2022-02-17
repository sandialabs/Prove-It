from .algebra import (HilbertSpaces, Qmult, QmultCodomain, Bra, Ket, 
                      NumBra, NumKet)
from .quantum_ops import Meas, QubitRegisterSpace, RegisterSU

# There is a tricky chicken-and-egg issue if we include these
# imports.  Let's just exclude them for now.
#from .circuits import (Gate, MultiQuditGate, Ghost,
#                       Input, Output, MultiWire, target)

#from .circuit import Gate, Input, Output, Target
# from .circuit import Circuit, MultiWire


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
