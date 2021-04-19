# Arithmetic and number theory concepts.

from .number_sets import (
    Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero,
    complex_polar_coordinates, 
    unit_length_complex_polar_angle)

from .number_sets import Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC
from .number_sets import e, pi, i, infinity
from .number_operation import NumberOperation
from .rounding import Floor, Ceil, Round
from .absolute_value import Abs
from .numerals import num, Numeral, DecimalSequence, Digits, DIGITS, is_literal_int
from .numerals import zero, one, two, three, four, five, six, seven, eight, nine, hexa, hexb, hexc, hexd, hexe, hexf
from .addition import (Add, subtract, dist_subtract, dist_add,
                       const_shift_decomposition, const_shift_composition)
from .negation import Neg
from .ordering import (NumberOrderingRelation, number_ordering,
                       Less, LessEq, greater, greater_eq, Min, Max)
from .multiplication import Mult
from .division import Div, frac
from .divisibility import Divides, DividesProper, GCD
from .modular import Mod, ModAbs
from .exponentiation import Exp, sqrt, sqrd
from .summation import Sum
from .product import Prod
from .integration import Integrate

import proveit

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    from .number_sets.natural_numbers import zero_in_nats
    from .numerals.decimals import less_0_1, less_1_2, less_2_3, less_3_4, less_4_5, less_5_6, less_6_7, less_7_8, less_8_9
    from .numerals.decimals import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
    from .numerals.decimals import posnat1, posnat2, posnat3, posnat4, posnat5, posnat6, posnat7, posnat8, posnat9
    from .negation import negated_zero
    from .number_sets.real_numbers import e_is_real_pos, pi_is_real_pos
    from .number_sets.complex_numbers import (
            i_is_complex, i_is_complex_nonzero)

# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
