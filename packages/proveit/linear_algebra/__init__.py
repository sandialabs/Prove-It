from .vector_spaces import (VecSpaces, deduce_as_vec_space,
                            containing_vec_space, including_vec_space)
from .vec_operation import (VecOperation, readily_factorable,
                            deduce_canonically_equal)
from .addition import VecAdd, VecSum, VecZero, vec_subtract
from .negation import VecNeg
from .scalar_multiplication import ScalarMult
from .vector_sets import (
        Span, SpanningSets, LinDepSets, Bases, Dim)
from .inner_products import (
        InnerProd, InnerProdSpaces, HilbertSpaces, Hspace,
        Norm, OrthoNormBases, OrthoProj, Adj, deduce_as_inner_prod_space)
from .linear_maps import (LinMap, LinMapAdd, Identity,
                          Commutator, AntiCommutator)
from .matrices import (MatrixSpace, MatrixMult, MatrixExp,
                       Unitary, SpecialUnitary, Diagonal)
from .tensors import TensorExp, TensorProd

# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

import proveit
if proveit.defaults.running_theory_notebook is None:
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    from . import (rational_set_is_vec_space, real_set_is_vec_space,
                   complex_set_is_vec_space)