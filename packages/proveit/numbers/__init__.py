# Arithmetic and number theory concepts.

from .number_sets import (
    ZeroSet, Natural, NaturalPos, Integer, IntegerEven,
    IntegerNonZero, IntegerNeg, IntegerNonPos, IntegerOdd,
    Prime, Rational, RationalNonZero, RationalPos, RationalNeg,
    RationalNonNeg, RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero, Conjugate,
    complex_polar_coordinates, 
    unit_length_complex_polar_angle)

from .number_sets import (
        Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC)
from .number_sets import e, pi, i, infinity
from .number_operation import (NumberOperation, readily_factorable,
                               deduce_in_number_set,
                               quick_simplified_index,
                               sorted_number_sets, 
                               readily_provable_number_set, deduce_number_set,
                               standard_number_set, standard_number_sets,
                               pos_number_set, neg_number_set, 
                               nonneg_number_set, nonpos_number_set,
                               nonzero_number_set,
                               union_number_set)
from .rounding import Floor, Ceil, Round
from .absolute_value import Abs
from .numerals import (num, Numeral, DecimalSequence, Digits, DIGITS,
                       BinarySequence, Bit, BITS, 
                       is_numeric_natural, is_numeric_int, 
                       is_numeric_rational,
                       numeric_rational_ints,
                       simplified_numeric_rational,
                       less_numeric_ints,
                       less_eq_numeric_ints,
                       less_numeric_rationals,
                       less_eq_numeric_rationals,
                       not_equal_numeric_rationals,
                       deduce_not_equal_numeric_rationals)
from .numerals import (zero, one, two, three, four, five, six, seven,
        eight, nine, hexa, hexb, hexc, hexd, hexe, hexf)
from .addition import (Add, subtract, dist_subtract, dist_add)
from .negation import Neg, negated
from .ordering import (NumberOrderingRelation, number_ordering,
                       Less, LessEq, greater, greater_eq, Min, Max)
from .multiplication import Mult, compose_product, remove_common_factors
from .division import Div, frac, compose_fraction
from .divisibility import Divides, DividesProper, GCD
from .modular import Mod, ModAbs
from .exponentiation import Exp, exp, exp2pi_i, sqrt, sqrd
from .logarithms import Log
from .summation import Sum
from .product import Prod
from .integration import Integrate

from .functions import (MonDecFuncs, deduce_as_mon_dec_func,
                        KroneckerDelta)

import proveit


if proveit.defaults.running_theory_notebook is None: # might include here 2 is even, 4 is even, etc
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    from .number_sets.natural_numbers import zero_in_nats
    from .number_sets.integers import (zero_is_int, zero_is_nonpos_int,
            zero_is_even, two_is_even, four_is_even, six_is_even,
            eight_is_even, one_is_odd, three_is_odd, five_is_odd,
            seven_is_odd, nine_is_odd)
    from .number_sets.rational_numbers import (
            zero_is_rational, zero_is_nonneg_rational, 
            zero_is_nonpos_rational)
    from .number_sets.real_numbers import (
            zero_is_real, zero_is_nonneg_real, zero_is_nonpos_real)
    from .number_sets.complex_numbers import zero_is_complex
    from .numerals.decimals import less_0_1, less_1_2, less_2_3, less_3_4, less_4_5, less_5_6, less_6_7, less_7_8, less_8_9
    from .numerals.decimals import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
    from .numerals.decimals import posnat1, posnat2, posnat3, posnat4, posnat5, posnat6, posnat7, posnat8, posnat9
    from .negation import negated_zero
    from .number_sets.real_numbers import e_is_real_pos, pi_is_real_pos
    from .number_sets.complex_numbers import (
            i_is_complex, i_is_complex_nonzero)
    from proveit.abstract_algebra.fields import (
            rational_field, real_field, complex_field)

# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())
