# Note: '>' and '>=' relations are expressed using Less and LessEq
# expression types using the direction='reversed' style variant.
from .less import Less, greater
from .less_eq import LessEq, greater_eq

from .max import Max
from .min import Min

# Total number ordering is internally represented as a
# conjunction of number relationships but formatted as, for example,
# a <= b < c = d <= e.
# number ordering is a funciton for creating such an expression
# with this formatting style.
from .number_ordering_relation import number_ordering


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
