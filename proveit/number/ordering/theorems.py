from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, BOOLEANS
from proveit.number import Integers, Reals, RealsPos
from proveit.number import GreaterThan, GreaterThanEquals, LessThan, LessThanEquals, Min, Max, Add, Sub, Neg, Mult, Fraction
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
                         GreaterThanEquals(a,b),
                         domain = Reals,
                         conditions = GreaterThan(a,b))
relaxGreaterThan

relaxLessThan = Forall([a,b],
                         LessThanEquals(a,b),
                         domain = Reals,
                         conditions = LessThan(a,b))
relaxLessThan

lessThanInBools = Forall([a, b], InSet(LessThan(a, b), BOOLEANS), domain=Reals)
lessThanInBools

lessThanEqualsInBools = Forall([a, b], InSet(LessThanEquals(a, b), BOOLEANS), domain=Reals)
lessThanEqualsInBools

greaterThanInBools = Forall([a, b], InSet(GreaterThan(a, b), BOOLEANS), domain=Reals)
greaterThanInBools

greaterThanEqualsInBools = Forall([a, b], InSet(GreaterThanEquals(a, b), BOOLEANS), domain=Reals)
greaterThanEqualsInBools

notEqualsIsLessThanOrGreaterThan = Forall((a, x), Or(LessThan(x, a), GreaterThan(x, a)), domain=Reals, conditions=[NotEquals(x, a)])
notEqualsIsLessThanOrGreaterThan

shiftLessThanToLessThanEquals = Forall((a, b), LessThanEquals(a, b), domain=Integers, conditions=[LessThan(Sub(a, one), b)])
shiftLessThanToLessThanEquals

lessThanEqualsAddRight = Forall([a, b, c], LessThanEquals(Add(a, c), Add(b, c)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddRight

lessThanEqualsAddLeft = Forall([a, b, c], LessThanEquals(Add(c, a), Add(c, b)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddLeft

lessThanEqualsSubtract = Forall([a, b, c], LessThanEquals(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsSubtract

lessThanAddRight = Forall([a, b, c], LessThan(Add(a, c), Add(b, c)), domain=Reals, conditions=[LessThan(a, b)])
lessThanAddRight

lessThanAddLeft = Forall([a, b, c], LessThan(Add(c, a), Add(c, b)), domain=Reals, conditions=[LessThan(a, b)])
lessThanAddLeft

lessThanSubtract = Forall([a, b, c], LessThan(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[LessThan(a, b)])
lessThanSubtract

greaterThanEqualsAddRight = Forall([a, b, c], GreaterThanEquals(Add(a, c), Add(b, c)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddRight

greaterThanEqualsAddLeft = Forall([a, b, c], GreaterThanEquals(Add(c, a), Add(c, b)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddLeft

greaterThanEqualsSubtract = Forall([a, b, c], GreaterThanEquals(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsSubtract

greaterThanAddRight = Forall([a, b, c], GreaterThan(Add(a, c), Add(b, c)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanAddRight

greaterThanAddLeft = Forall([a, b, c], GreaterThan(Add(c, a), Add(c, b)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanAddLeft

greaterThanSubtract = Forall([a, b, c], GreaterThan(Sub(a, c), Sub(b, c)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanSubtract

negatedLessThan = Forall([a, b], GreaterThan(Neg(a), Neg(b)), domain=Reals, conditions=[LessThan(a, b)])
negatedLessThan

negatedLessThanEquals = Forall([a, b], GreaterThanEquals(Neg(a), Neg(b)), domain=Reals, conditions=[LessThanEquals(a, b)])
negatedLessThanEquals

negatedGreaterThan = Forall([a, b], LessThan(Neg(a), Neg(b)), domain=Reals, conditions=[GreaterThan(a, b)])
negatedGreaterThan

negatedGreaterThanEquals = Forall([a, b], LessThanEquals(Neg(a), Neg(b)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
negatedGreaterThanEquals

endTheorems(locals(), __package__)
