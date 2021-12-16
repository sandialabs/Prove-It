from .qcircuit import Qcircuit
from .qcircuit_elements import (Gate, MultiQuditGate, Ghost,
                                Input, Output, MultiWire)
from .qcircuit_equiv import QcircuitEquiv


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
