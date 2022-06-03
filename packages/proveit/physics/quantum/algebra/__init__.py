from .bra_ket import Bra, Ket, NumBra, NumKet
from .qmult import Qmult
import proveit


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

if proveit.defaults.sideeffect_automation:
    # Import some fundamental theorems without quantifiers
    from . import (complex_set_is_hilbert_space,
                   ket_zero_in_qubit_space,
                   ket_one_in_qubit_space,
                   ket_zero_norm, ket_one_norm,
                   ket_zero_and_one_are_orthogonal)
