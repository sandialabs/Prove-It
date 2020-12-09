from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, Boolean
from proveit.numbers import Integer, Real, RealPos
from proveit.numbers import Greater, GreaterEq, Less, LessEq, Min, Max, Add, Sub, Neg, Mult, frac
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
                         GreaterEq(a,b),
                         domain = Real,
                         conditions = Greater(a,b))
relaxGreaterThan

relaxLessThan = Forall([a,b],
                         LessEq(a,b),
                         domain = Real,
                         conditions = Less(a,b))
relaxLessThan

lessThanInBool = Forall([a, b], InSet(Less(a, b), Boolean), domain=Real)
lessThanInBool

lessThanEqualsInBool = Forall([a, b], InSet(LessEq(a, b), Boolean), domain=Real)
lessThanEqualsInBool

greaterThanInBool = Forall([a, b], InSet(Greater(a, b), Boolean), domain=Real)
greaterThanInBool

greaterThanEqualsInBool = Forall([a, b], InSet(GreaterEq(a, b), Boolean), domain=Real)
greaterThanEqualsInBool

notEqualsIsLessThanOrGreaterThan = Forall((a, x), Or(Less(x, a), Greater(x, a)), domain=Real, conditions=[NotEquals(x, a)])
notEqualsIsLessThanOrGreaterThan

shiftLessThanToLessThanEquals = Forall((a, b), LessEq(a, b), domain=Integer, conditions=[Less(Sub(a, one), b)])
shiftLessThanToLessThanEquals

lessThanEqualsAddRight = Forall([a, b, c], LessEq(Add(a, c), Add(b, c)), domain=Real, conditions=[LessEq(a, b)])
lessThanEqualsAddRight

lessThanEqualsAddLeft = Forall([a, b, c], LessEq(Add(c, a), Add(c, b)), domain=Real, conditions=[LessEq(a, b)])
lessThanEqualsAddLeft

lessThanEqualsSubtract = Forall([a, b, c], LessEq(Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessEq(a, b)])
lessThanEqualsSubtract

lessThanAddRight = Forall([a, b, c], Less(Add(a, c), Add(b, c)), domain=Real, conditions=[Less(a, b)])
lessThanAddRight

lessThanAddLeft = Forall([a, b, c], Less(Add(c, a), Add(c, b)), domain=Real, conditions=[Less(a, b)])
lessThanAddLeft

lessThanSubtract = Forall([a, b, c], Less(Sub(a, c), Sub(b, c)), domain=Real, conditions=[Less(a, b)])
lessThanSubtract

greaterThanEqualsAddRight = Forall([a, b, c], GreaterEq(Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterEq(a, b)])
greaterThanEqualsAddRight

greaterThanEqualsAddLeft = Forall([a, b, c], GreaterEq(Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterEq(a, b)])
greaterThanEqualsAddLeft

greaterThanEqualsSubtract = Forall([a, b, c], GreaterEq(Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterEq(a, b)])
greaterThanEqualsSubtract

greaterThanAddRight = Forall([a, b, c], Greater(Add(a, c), Add(b, c)), domain=Real, conditions=[Greater(a, b)])
greaterThanAddRight

greaterThanAddLeft = Forall([a, b, c], Greater(Add(c, a), Add(c, b)), domain=Real, conditions=[Greater(a, b)])
greaterThanAddLeft

greaterThanSubtract = Forall([a, b, c], Greater(Sub(a, c), Sub(b, c)), domain=Real, conditions=[Greater(a, b)])
greaterThanSubtract

negatedLessThan = Forall([a, b], Greater(Neg(a), Neg(b)), domain=Real, conditions=[Less(a, b)])
negatedLessThan

negatedLessThanEquals = Forall([a, b], GreaterEq(Neg(a), Neg(b)), domain=Real, conditions=[LessEq(a, b)])
negatedLessThanEquals

negatedGreaterThan = Forall([a, b], Less(Neg(a), Neg(b)), domain=Real, conditions=[Greater(a, b)])
negatedGreaterThan

negatedGreaterThanEquals = Forall([a, b], LessEq(Neg(a), Neg(b)), domain=Real, conditions=[GreaterEq(a, b)])
negatedGreaterThanEquals

endTheorems(locals(), __package__)
