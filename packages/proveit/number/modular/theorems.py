from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Iff, And, SetOfAll
from proveit.number import Integers, Interval, Reals, RealsPos, Complexes
from proveit.number import Abs, Mod, ModAbs, GreaterThanEquals, LessThanEquals, Add, Sub, Neg, Mult, frac, IntervalCO
from proveit.common import a, b, c, x, y, N, xEtc, xMulti
from proveit.number.common import zero, one
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

# transferred by wdc 3/11/2020
modIntClosure = Forall((a, b), InSet(Mod(a, b), Integers), domain=Integers)
modIntClosure

# transferred by wdc 3/11/2020
modInInterval = Forall((a, b), InSet(Mod(a, b), Interval(zero, Sub(b, one))), domain=Integers)
modInInterval

# transferred by wdc 3/11/2020
modRealClosure = Forall((a, b), InSet(Mod(a, b), Reals), domain=Reals)
modRealClosure

# transferred by wdc 3/11/2020
modAbsRealClosure = Forall((a, b), InSet(ModAbs(a, b), Reals), domain=Reals)
modAbsRealClosure

# transferred by wdc 3/11/2020
absComplexClosure = Forall([a], InSet(Abs(a), Reals), domain=Complexes)
absComplexClosure

# transferred by wdc 3/11/2020
absNonzeroClosure = Forall([a], InSet(Abs(a), RealsPos), domain=Complexes, conditions=[NotEquals(a, zero)])
absNonzeroClosure

# transferred by wdc 3/11/2020
modInIntervalCO = Forall((a, b), InSet(Mod(a, b), IntervalCO(zero, b)), domain=Reals)
modInIntervalCO

# transferred by wdc 3/11/2020
absIsNonNeg = Forall(a, GreaterThanEquals(Abs(a), zero), domain=Complexes)
absIsNonNeg

# transferred by wdc 3/11/2020
absNotEqZero = Forall([a], NotEquals(Abs(a), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
absNotEqZero

# transferred by wdc 3/11/2020
absElim = Forall(x, Equals(Abs(x), x),
                domain = RealsPos)
absElim

# transferred by wdc 3/11/2020
absIneq = Forall((x, y), Iff(LessThanEquals(Abs(x), y), 
                             And(LessThanEquals(Neg(y), x), LessThanEquals(x, y))),
                 domain = Reals, conditions=[GreaterThanEquals(y, zero)])
absIneq

# transferred by wdc 3/11/2020
triangleInequality = Forall([a,b],
                        LessThanEquals(Abs(Add(a,b)),Add(Abs(a),Abs(b))),
                        domain=Complexes)
triangleInequality

# transferred by wdc 3/11/2020
absProd = Forall(xEtc,
                 Equals(Abs(Mult(xEtc)),
                        Mult(Etcetera(Abs(xMulti)))),
                 domain = Complexes)
absProd

# transferred by wdc 3/11/2020
absFrac = Forall([a,b],
                 Equals(Abs(frac(a,b)),frac(Abs(a),Abs(b))),
                 domain = Complexes)
absFrac

# transferred by wdc 3/11/2020
modAbsScaled = Forall((a, b, c), Equals(Mult(a, ModAbs(b, c)), ModAbs(Mult(a, b), Mult(a, c))), domain=Reals)
modAbsScaled

# transferred by wdc 3/11/2020
modAbsSubtractCancel = Forall((a, b, c), LessThanEquals(ModAbs(Sub(Mod(Add(b, a), c), b), c), 
                                                        Abs(a)),
                              domain=Reals)
modAbsSubtractCancel

# transferred by wdc 3/11/2020
fullModularRangeEquiv = Forall((N, a, b), 
                               Equals(SetOfAll(x, Mod(x, N), domain=Interval(a, b)), 
                                      Interval(zero, Sub(N, one))),
                               domain=Integers, conditions=[Equals(Sub(b, a), Sub(N, one))])
fullModularRangeEquiv

# transferred by wdc 3/11/2020
fullModularRangeEquivLeftShift = Forall((N, a, b, c), 
                               Equals(SetOfAll(x, Mod(Add(c, x), N), domain=Interval(a, b)), 
                                      Interval(zero, Sub(N, one))),
                               domain=Integers, conditions=[Equals(Sub(b, a), Sub(N, one))])
fullModularRangeEquivLeftShift

# transferred by wdc 3/11/2020
fullModularRangeEquivRightShift = Forall((N, a, b, c), 
                               Equals(SetOfAll(x, Mod(Add(x, c), N), domain=Interval(a, b)), 
                                      Interval(zero, Sub(N, one))),
                               domain=Integers, conditions=[Equals(Sub(b, a), Sub(N, one))])
fullModularRangeEquivRightShift


endTheorems(locals(), __package__)
