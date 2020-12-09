from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.numbers import Neg, Integer, Real, Complex, Add, Sub, Mult, LessThan, GreaterThan
from proveit.common import a, b, x, y, xEtc, xMulti
from proveit.numbers.common import zero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

negIntClosure = Forall(a, InSet(Neg(a), Integer), domain=Integer)
negIntClosure

negRealClosure = Forall(a, InSet(Neg(a), Real), domain=Real)
negRealClosure

negComplexClosure = Forall(a, InSet(Neg(a), Complex), domain=Complex)
negComplexClosure

negatedPositiveIsNegative = Forall(a, LessThan(Neg(a), zero), domain=Real, conditions=[GreaterThan(a, zero)])
negatedPositiveIsNegative

negatedNegativeIsPositive = Forall(a, GreaterThan(Neg(a), zero), domain=Real, conditions=[LessThan(a, zero)])
negatedNegativeIsPositive

negNotEqZero = Forall(a, NotEquals(Neg(a), zero), domain=Complex, conditions=[NotEquals(a, zero)])
negNotEqZero

distributeNegThroughSum = Forall([xEtc], Equals(Neg(Add(xEtc)),
                                               Add(Etcetera(Neg(xMulti)))),
                                 domain=Complex)
distributeNegThroughSum


distributeNegThroughSumRev = Forall([xEtc], 
                                    Equals(Add(Etcetera(Neg(xMulti))),
                                           Neg(Add(xEtc))),
                                 domain=Complex)
distributeNegThroughSumRev

distributeNegThroughSubtract = Forall([x, y], Equals(Neg(Sub(x, y)),
                                               Add(Neg(x), y)),
                                 domain=Complex)
distributeNegThroughSubtract

negTimesPos = Forall([x, y], Equals(Mult(Neg(x), y), Neg(Mult(x, y))), domain=Complex)
negTimesPos

negTimesPosRev = Forall([x, y], Equals(Neg(Mult(x, y)), Mult(Neg(x), y)), domain=Complex)
negTimesPosRev

posTimesNeg = Forall([x, y], Equals(Mult(x, Neg(y)), Neg(Mult(x, y))), domain=Complex)
posTimesNeg

posTimesNegRev = Forall([x, y], Equals(Neg(Mult(x, y)), Mult(x, Neg(y))), domain=Complex)
posTimesNegRev

negTimesNeg = Forall([x, y], Equals(Mult(Neg(x), Neg(y)), Mult(x, y)), domain=Complex)
negTimesNeg

negNeg = Forall([a],
                 Equals(Neg(Neg(a)), a),
                domain=Complex)
negNeg

negZero = Equals(Neg(zero), zero)
negZero

cancelAddNeg = Forall([a,b],
                      Equals(Add(Add(a,b),Neg(b)), a),
                      domain=Complex)
cancelAddNeg


endTheorems(locals(), __package__)
