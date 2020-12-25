from .membership import InSet, NotInSet, Membership, Nonmembership
from .enumeration import Set
# StrictSubset and SubsetProper are aliases for ProperSubset.
# StrictSuperset and SupersetProper are aliases for ProperSuperset.
from .inclusion import (
    SubsetEq, NotSubsetEq, ProperSubset, StrictSubset, SubsetProper,
    NotProperSubset, SupersetEq, NotSupersetEq, ProperSuperset,
    StrictSuperset, SupersetProper, NotProperSuperset)
from .equivalence import SetEquiv, SetNotEquiv
from .unification import Union, UnionAll
from .intersection import Intersect, IntersectAll
from .subtraction import Difference
from .comprehension import SetOfAll
from .power_set import PowerSet
from .disjointness import Disjoint, Distinct
from .cardinality import Card


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
