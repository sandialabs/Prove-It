from .integers import (
        Integer, IntegerNeg, IntegerNonZero, IntegerNonPos,
        Interval, infinity)
from .natural_numbers import Natural, NaturalPos
from .rational_numbers import (Rational, RationalNonZero,
                               RationalPos, RationalNeg,
                               RationalNonNeg, RationalNonPos)
from .real_numbers import (
    Real, RealNonZero, RealPos, RealNeg, RealNonNeg, RealNonPos,
    RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC,
    e, pi)
from .complex_numbers import Complex, ComplexNonZero, i


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
