from proveit import Etcetera
from proveit.logic import Forall, InSet, NotEquals, Equals
from proveit.numbers import Sub, Natural, NaturalPos, Integer, Real, Complex, Add, Neg, GreaterThan, GreaterThanEquals
from proveit.common import a, b, w, x, y, z, xEtc, yEtc, vEtc, wEtc, zEtc, yMulti
from proveit.numbers.common import zero, one
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

subtractIntClosure = Forall([a, b], InSet(Sub(a, b), Integer), domain=Integer)
subtractIntClosure

subtractClosureNats = Forall([a, b], InSet(Sub(a, b), Natural), domain=Integer, conditions=[GreaterThanEquals(a, b)])
subtractClosureNats

subtractClosureNatsPos = Forall([a, b], InSet(Sub(a, b), NaturalPos), domain=Integer, conditions=[GreaterThan(a, b)])
subtractClosureNatsPos

subtractComplexClosure = Forall([a, b], InSet(Sub(a, b), Complex), domain=Complex)
subtractComplexClosure

subtractRealClosure = Forall([a, b], InSet(Sub(a, b), Real), domain=Real)
subtractRealClosure

subtractOneInNats = Forall(a, InSet(Sub(a, one), Natural), domain=NaturalPos)
subtractOneInNats

diffNotEqZero = Forall((a, b), NotEquals(Sub(a, b), zero), domain=Complex, conditions=[NotEquals(a, b)])
diffNotEqZero

subtractAsAddNeg = Forall([x, y], Equals(Sub(x, y), 
                                         Add(x, Neg(y))), 
                          domain=Complex)
subtractAsAddNeg

addNegAsSubtract = Forall([x, y], Equals(Add(x, Neg(y)),
                                         Sub(x, y)), 
                          domain=Complex)
addNegAsSubtract


absorbTermsIntoSubtraction = Forall([wEtc, x, y, zEtc],
                                    Equals(Add(wEtc, Sub(x, y), zEtc),
                                           Sub(Add(wEtc, x, zEtc), y)), domain=Complex)
absorbTermsIntoSubtraction


subtractCancelElimSums = Forall([x, y, z], 
                        Equals(Sub(Add(x, y), Add(x, z)),
                              Sub(y, z)), domain=Complex)
subtractCancelElimSums

subtractCancelElimLeftSum = Forall([w, x, yEtc, zEtc], 
                        Equals(Sub(Add(w, x), Add(yEtc, w, zEtc)),
                              Sub(x, Add(yEtc, zEtc))), domain=Complex)
subtractCancelElimLeftSum

subtractCancelElimRightSum = Forall([wEtc, x, yEtc, z], 
                        Equals(Sub(Add(wEtc, x, yEtc), Add(x, z)),
                              Sub(Add(wEtc, yEtc), z)), domain=Complex)
subtractCancelElimRightSum

subtractCancelTwoSums = Forall([vEtc, w, xEtc, yEtc, zEtc], 
                        Equals(Sub(Add(vEtc, w, xEtc), Add(yEtc, w, zEtc)),
                              Sub(Add(vEtc, xEtc), Add(yEtc, zEtc))), domain=Complex)
subtractCancelTwoSums

subtractCancelLeftSum = Forall([xEtc, y, zEtc], 
                        Equals(Sub(Add(xEtc, y, zEtc), y),
                               Add(xEtc, zEtc)), domain=Complex)
subtractCancelLeftSum

subtractCancelRightSum = Forall([xEtc, y, zEtc], 
                        Equals(Sub(y, Add(xEtc, y, zEtc)),
                               Neg(Add(xEtc, zEtc))), domain=Complex)
subtractCancelRightSum

subtractCancelRightSumSingleRight = Forall([x, y], Equals(Sub(y, Add(y, x)), Neg(x)), domain=Complex)
subtractCancelRightSumSingleRight

subtractCancelRightSumSingleLeft = Forall([x, y], Equals(Sub(y, Add(x, y)), Neg(x)), domain=Complex)
subtractCancelRightSumSingleLeft

subtractCancelLeftSumSingleRight = Forall([x, y], Equals(Sub(Add(y, x), y), x), domain=Complex)
subtractCancelLeftSumSingleRight

subtractCancelLeftSumSingleLeft = Forall([x, y], Equals(Sub(Add(x, y), y), x), domain=Complex)
subtractCancelLeftSumSingleLeft

subtractCancelComplete = Forall(x, Equals(Sub(x, x), zero), domain=Complex)
subtractCancelComplete

distributeSubtraction = Forall([x, yEtc],
                              Equals(Sub(x, Add(yEtc)),
                                    Add(x, Etcetera(Neg(yMulti)))),
                              domain=Complex)
distributeSubtraction

cancelAddition = Forall([a,b],
                        Equals(Add(a, Sub(b,b)), a),
                       domain=Complex)
cancelAddition

cancelSubAndAdd = Forall([a,b],
                         Equals(Sub(Sub(a,Neg(b)), b), a),
                        domain=Complex)
cancelSubAndAdd

cancelSubThenAdd = Forall([a,b],
                        Equals(Add(Sub(a,b), b), a),
                       domain=Complex)
cancelSubThenAdd

convertAddNegToSub = Forall([a,b],
                            Equals(Add(a,Neg(b)), Sub(a,b)),
                            domain=Complex)
convertAddNegToSub

endTheorems(locals(), __package__)
