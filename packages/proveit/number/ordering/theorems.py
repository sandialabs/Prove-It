from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, Booleans
from proveit.number import Integers, Reals, RealsPos
from proveit.number import Greater, GreaterEq, Less, LessEq, Min, Max, Add, Sub, Neg, Mult, Fraction
from proveit.common import a, b, c, d, x
from proveit.number.common import zero, one
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

minRealClosure = Forall((a, b), InSet(Min(a, b), Reals), domain=Reals)
minRealClosure

minRealPosClosure = Forall((a, b), InSet(Min(a, b), RealsPos), domain=RealsPos)
minRealPosClosure

maxRealClosure = Forall((a, b), InSet(Max(a, b), Reals), domain=Reals)
maxRealClosure

maxRealPosClosure = Forall((a, b), InSet(Max(a, b), RealsPos), domain=RealsPos)
maxRealPosClosure

relaxGreaterThan = Forall([a,b],
                         GreaterEq(a,b),
                         domain = Reals,
                         conditions = Greater(a,b))
relaxGreaterThan

relaxLessThan = Forall([a,b],
                         LessEq(a,b),
                         domain = Reals,
                         conditions = Less(a,b))
relaxLessThan

lessThanInBools = Forall([a, b], InSet(Less(a, b), Booleans), domain=Reals)
lessThanInBools

lessThanEqualsInBools = Forall([a, b], InSet(LessEq(a, b), Booleans), domain=Reals)
lessThanEqualsInBools

greaterThanInBools = Forall([a, b], InSet(Greater(a, b), Booleans), domain=Reals)
greaterThanInBools

greaterThanEqualsInBools = Forall([a, b], InSet(GreaterEq(a, b), Booleans), domain=Reals)
greaterThanEqualsInBools

notEqualsIsLessThanOrGreaterThan = Forall((a, x), Or(Less(x, a), Greater(x, a)), domain=Reals, conditions=[NotEquals(x, a)])
notEqualsIsLessThanOrGreaterThan

shiftLessThanToLessThanEquals = Forall((a, b), LessEq(a, b), domain=Integers, conditions=[Less(Sub(a, one), b)])
shiftLessThanToLessThanEquals

lessThanEqualsAddRight = Forall([a, b, c], LessEq(Add(a, c), Add(b, c)), domain=Reals, conditions=[LessEq(a, b)])
lessThanEqualsAddRight

lessThanEqualsAddLeft = Forall([a, b, c], LessEq(Add(c, a), Add(c, b)), domain=Reals, conditions=[LessEq(a, b)])
lessThanEqualsAddLeft

lessThanEqualsSubtract = Forall([a, b, c], LessEq(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[LessEq(a, b)])
lessThanEqualsSubtract

lessThanAddRight = Forall([a, b, c], Less(Add(a, c), Add(b, c)), domain=Reals, conditions=[Less(a, b)])
lessThanAddRight

lessThanAddLeft = Forall([a, b, c], Less(Add(c, a), Add(c, b)), domain=Reals, conditions=[Less(a, b)])
lessThanAddLeft

lessThanSubtract = Forall([a, b, c], Less(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[Less(a, b)])
lessThanSubtract

greaterThanEqualsAddRight = Forall([a, b, c], GreaterEq(Add(a, c), Add(b, c)), domain=Reals, conditions=[GreaterEq(a, b)])
greaterThanEqualsAddRight

greaterThanEqualsAddLeft = Forall([a, b, c], GreaterEq(Add(c, a), Add(c, b)), domain=Reals, conditions=[GreaterEq(a, b)])
greaterThanEqualsAddLeft

greaterThanEqualsSubtract = Forall([a, b, c], GreaterEq(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[GreaterEq(a, b)])
greaterThanEqualsSubtract

greaterThanAddRight = Forall([a, b, c], Greater(Add(a, c), Add(b, c)), domain=Reals, conditions=[Greater(a, b)])
greaterThanAddRight

greaterThanAddLeft = Forall([a, b, c], Greater(Add(c, a), Add(c, b)), domain=Reals, conditions=[Greater(a, b)])
greaterThanAddLeft

greaterThanSubtract = Forall([a, b, c], Greater(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[Greater(a, b)])
greaterThanSubtract

negatedLessThan = Forall([a, b], Greater(Neg(a), Neg(b)), domain=Reals, conditions=[Less(a, b)])
negatedLessThan

negatedLessThanEquals = Forall([a, b], GreaterEq(Neg(a), Neg(b)), domain=Reals, conditions=[LessEq(a, b)])
negatedLessThanEquals

negatedGreaterThan = Forall([a, b], Less(Neg(a), Neg(b)), domain=Reals, conditions=[Greater(a, b)])
negatedGreaterThan

negatedGreaterThanEquals = Forall([a, b], LessEq(Neg(a), Neg(b)), domain=Reals, conditions=[GreaterEq(a, b)])
negatedGreaterThanEquals

endTheorems(locals(), __package__)
