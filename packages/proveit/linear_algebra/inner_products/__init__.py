from .inner_prod_spaces import InnerProdSpaces, deduce_as_inner_prod_space
from .inner_prod import InnerProd
from .norm import Norm


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
    from . import (rational_set_is_inner_prod_space, 
                   real_set_is_inner_prod_space,
                   complex_set_is_inner_prod_space)
