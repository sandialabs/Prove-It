# Arithmetic and number theory concepts.

from .sets import Integers, Naturals, NaturalsPos, Len, Reals, RealsNeg, RealsPos, Complexes
from .sets import Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC
from .sets import e, pi, i, infinity
from .numeral import Numeral, num, WholeDecimal
from .numeral import zero, one, two, three, four, five, six, seven, eight, nine, hexa, hexb, hexc, hexd, hexe, hexf
from .addition import Add
from .subtraction import Subtract
from .negation import Neg
from .multiplication import Mult
from .division import Divide, Frac
from .exponentiation import Exp, Sqrt
from .summation import Sum
from .integration import Integrate
from .modular import Abs, Mod, ModAbs
from .rounding import Floor, Ceil, Round
from .ordering import Less, LessEq, LesserSequence, Greater, GreaterEq, GreaterSequence, Min, Max

import proveit

try:
    # Import some fundamental theorems without quantifiers.
    # Fails before running the corresponding _axioms_/_theorems_ notebooks for the first time, but fine after that.
    from .boolean.negation._theorems_ import notFalse, notF, notT, notTimpliesF
    from .boolean.implication._theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
    from .boolean._axioms_ import trueAxiom, boolsDef, falseNotTrue
    from .boolean._theorems_ import trueEqTrue, falseEqFalse, trueNotFalse, trueInBool, falseInBool
except:
    pass
