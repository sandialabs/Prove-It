from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.number import Neg, Integers, Reals, Complexes, Add, Sub, Mult, LessThan, GreaterThan
from proveit.common import a, b, x, y, xEtc, xMulti
from proveit.number.common import zero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

negIntClosure = Forall(a, InSet(Neg(a), Integers), domain=Integers)
negIntClosure

negRealClosure = Forall(a, InSet(Neg(a), Reals), domain=Reals)
negRealClosure

negComplexClosure = Forall(a, InSet(Neg(a), Complexes), domain=Complexes)
negComplexClosure

negatedPositiveIsNegative = Forall(a, LessThan(Neg(a), zero), domain=Reals, conditions=[GreaterThan(a, zero)])
negatedPositiveIsNegative

negatedNegativeIsPositive = Forall(a, GreaterThan(Neg(a), zero), domain=Reals, conditions=[LessThan(a, zero)])
negatedNegativeIsPositive

negNotEqZero = Forall(a, NotEquals(Neg(a), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
negNotEqZero

distributeNegThroughSum = Forall([xEtc], Equals(Neg(Add(xEtc)),
                                               Add(Etcetera(Neg(xMulti)))),
                                 domain=Complexes)
distributeNegThroughSum


distributeNegThroughSumRev = Forall([xEtc], 
                                    Equals(Add(Etcetera(Neg(xMulti))),
                                           Neg(Add(xEtc))),
                                 domain=Complexes)
distributeNegThroughSumRev

distributeNegThroughSubtract = Forall([x, y], Equals(Neg(Sub(x, y)),
                                               Add(Neg(x), y)),
                                 domain=Complexes)
distributeNegThroughSubtract

negTimesPos = Forall([x, y], Equals(Mult(Neg(x), y), Neg(Mult(x, y))), domain=Complexes)
negTimesPos

negTimesPosRev = Forall([x, y], Equals(Neg(Mult(x, y)), Mult(Neg(x), y)), domain=Complexes)
negTimesPosRev

posTimesNeg = Forall([x, y], Equals(Mult(x, Neg(y)), Neg(Mult(x, y))), domain=Complexes)
posTimesNeg

posTimesNegRev = Forall([x, y], Equals(Neg(Mult(x, y)), Mult(x, Neg(y))), domain=Complexes)
posTimesNegRev

negTimesNeg = Forall([x, y], Equals(Mult(Neg(x), Neg(y)), Mult(x, y)), domain=Complexes)
negTimesNeg

negNeg = Forall([a],
                 Equals(Neg(Neg(a)), a),
                domain=Complexes)
negNeg

negZero = Equals(Neg(zero), zero)
negZero

cancelAddNeg = Forall([a,b],
                      Equals(Add(Add(a,b),Neg(b)), a),
                      domain=Complexes)
cancelAddNeg


endTheorems(locals(), __package__)
