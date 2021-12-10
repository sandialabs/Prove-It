# still working on: the ModAdd class
from .phase_est_ops import (ModAdd, Pfail, PhaseEst, Psuccess, 
                            QPE, QPE1, SubIndexed)


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
