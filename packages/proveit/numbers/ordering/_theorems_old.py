from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, Boolean
from proveit.numbers import Integer, Real, RealPos
from proveit.numbers import GreaterThan, GreaterThanEquals, LessThan, LessThanEquals, Min, Max, Add, Sub, Neg, Mult, frac
from proveit.common import a, b, c, d, x
from proveit.numbers.common import zero, one
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

minRealClosure = Forall((a, b), InSet(Min(a, b), Real), domain=Real)
minRealClosure

minRealPosClosure = Forall((a, b), InSet(Min(a, b), RealPos), domain=RealPos)
minRealPosClosure

maxRealClosure = Forall((a, b), InSet(Max(a, b), Real), domain=Real)
maxRealClosure

maxRealPosClosure = Forall((a, b), InSet(Max(a, b), RealPos), domain=RealPos)
maxRealPosClosure

relaxGreaterThan = Forall([a,b],
                         GreaterThanEquals(a,b),
                         domain = Real,
                         conditions = GreaterThan(a,b))
relaxGreaterThan

relaxLessThan = Forall([a,b],
                         LessThanEquals(a,b),
                         domain = Real,
                         conditions = LessThan(a,b))
relaxLessThan

lessThanInBool = Forall([a, b], InSet(LessThan(a, b), Boolean), domain=Real)
lessThanInBool

lessThanEqualsInBool = Forall([a, b], InSet(LessThanEquals(a, b), Boolean), domain=Real)
lessThanEqualsInBool

greaterThanInBool = Forall([a, b], InSet(GreaterThan(a, b), Boolean), domain=Real)
greaterThanInBool

greaterThanEqualsInBool = Forall([a, b], InSet(GreaterThanEquals(a, b), Boolean), domain=Real)
greaterThanEqualsInBool

notEqualsIsLessThanOrGreaterThan = Forall((a, x), Or(LessThan(x, a), GreaterThan(x, a)), domain=Real, conditions=[NotEquals(x, a)])
notEqualsIsLessThanOrGreaterThan

shiftLessThanToLessThanEquals = Forall((a, b), LessThanEquals(a, b), domain=Integer, conditions=[LessThan(Sub(a, one), b)])
shiftLessThanToLessThanEquals

lessThanEqualsAddRight = Forall([a, b, c], LessThanEquals(Add(a, c), Add(b, c)), domain=Real, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddRight

lessThanEqualsAddLeft = Forall([a, b, c], LessThanEquals(Add(c, a), Add(c, b)), domain=Real, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddLeft

lessThanEqualsSubtract = Forall([a, b, c], LessThanEquals(Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessThanEquals(a, b)])
lessThanEqualsSubtract

lessThanAddRight = Forall([a, b, c], LessThan(Add(a, c), Add(b, c)), domain=Real, conditions=[LessThan(a, b)])
lessThanAddRight

lessThanAddLeft = Forall([a, b, c], LessThan(Add(c, a), Add(c, b)), domain=Real, conditions=[LessThan(a, b)])
lessThanAddLeft

lessThanSubtract = Forall([a, b, c], LessThan(Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessThan(a, b)])
lessThanSubtract

greaterThanEqualsAddRight = Forall([a, b, c], GreaterThanEquals(Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddRight

greaterThanEqualsAddLeft = Forall([a, b, c], GreaterThanEquals(Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddLeft

greaterThanEqualsSubtract = Forall([a, b, c], GreaterThanEquals(Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsSubtract

greaterThanAddRight = Forall([a, b, c], GreaterThan(Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterThan(a, b)])
greaterThanAddRight

greaterThanAddLeft = Forall([a, b, c], GreaterThan(Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterThan(a, b)])
greaterThanAddLeft

greaterThanSubtract = Forall([a, b, c], GreaterThan(Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterThan(a, b)])
greaterThanSubtract

negatedLessThan = Forall([a, b], GreaterThan(Neg(a), Neg(b)), domain=Real, conditions=[LessThan(a, b)])
negatedLessThan

negatedLessThanEquals = Forall([a, b], GreaterThanEquals(Neg(a), Neg(b)), domain=Real, conditions=[LessThanEquals(a, b)])
negatedLessThanEquals

negatedGreaterThan = Forall([a, b], LessThan(Neg(a), Neg(b)), domain=Real, conditions=[GreaterThan(a, b)])
negatedGreaterThan

negatedGreaterThanEquals = Forall([a, b], LessThanEquals(Neg(a), Neg(b)), domain=Real, conditions=[GreaterThanEquals(a, b)])
negatedGreaterThanEquals

endTheorems(locals(), __package__)
