from .integers import Integer, Interval, infinity
from .natural_numbers import Natural, NaturalPos
from .rational_numbers import (Rational, RationalNonZero, RationalNeg,
                               RationalNonNeg, RationalPos)
from .real_numbers import (
    Real,
    RealNeg,
    RealNonNeg,
    RealPos,
    RealInterval,
    IntervalOO,
    IntervalCC,
    IntervalCO,
    IntervalOC,
    e,
    pi)
from .complex_numbers import Complex, i


# KEEP THE FOLLOWING AT THE BOTTOM OF THIS __init__.py.
#  (Additions may be made above)
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
