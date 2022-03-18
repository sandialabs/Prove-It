from .vector_spaces import (VecSpaces, deduce_as_vec_space,
                            containing_vec_space, including_vec_space)
from .addition import VecAdd, VecSum, VecZero
from .negation import VecNeg
from .scalar_multiplication import ScalarMult
from .inner_products import (InnerProdSpaces, InnerProd, Norm,
                             deduce_as_inner_prod_space)
from .linear_maps import LinMap, LinMapAdd
from .matrices import (MatrixSpace, MatrixMult, MatrixExp,
                       Unitary, SpecialUnitary)
from .tensors import TensorExp, TensorProd


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

import proveit
if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers
    from . import (rational_set_is_vec_space, real_set_is_vec_space,
                   complex_set_is_vec_space)