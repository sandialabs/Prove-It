from .subset import SubsetEq, NotSubsetEq
# StrictSubset and SubsetProper are aliased for ProperSubset
from .subset import ProperSubset, StrictSubset, SubsetProper
from .subset import NotProperSubset
from .superset import SupersetEq, NotSupersetEq
# StrictSuperset and SupersetProper are aliased for ProperSuperset
from .superset import ProperSuperset, StrictSuperset, SupersetProper
from .superset import NotProperSuperset


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
