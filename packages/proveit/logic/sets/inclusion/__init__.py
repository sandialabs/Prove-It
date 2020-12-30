# superset_eq creates a SubsetEq object with a 
# direction='reversed' style.
from .subset_eq import SubsetEq, superset_eq

# not_superset_eq creates a NotSubsetEq object with a
# direction='reversed' style.
from .not_subset_eq import NotSubsetEq, not_superset_eq

# StrictSubset and SubsetProper are aliased for ProperSubset
# proper_superset creates a ProperSubset object with a
# direction='reversed' style.
from .proper_subset import (ProperSubset, StrictSubset, SubsetProper,
                            proper_superset)

# not_proper_superset creates a NotProperSubset with a
# direction='reversed' style.
from .not_proper_subset import (NotProperSubset, not_proper_superset)

# Total ordering for set inclusion is internally represented as
# conjunction of set relationships but formatted as, for example,
# A proper_subset B subset_eq C set_equiv D subset_eq E.
# inclusion_ordering is a funciton for creating such an expression
# with this formatting style.
from .inclusion_relation import inclusion_ordering

# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
