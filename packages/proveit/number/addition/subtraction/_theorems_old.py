from proveit import Etcetera
from proveit.logic import Forall, InSet, NotEquals, Equals
from proveit.number import Sub, Natural, NaturalPos, Integers, Reals, Complexes, Add, Neg, GreaterThan, GreaterThanEquals
from proveit.common import a, b, w, x, y, z, xEtc, yEtc, vEtc, wEtc, zEtc, yMulti
from proveit.number.common import zero, one
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

subtractIntClosure = Forall([a, b], InSet(Sub(a, b), Integers), domain=Integers)
subtractIntClosure

subtractClosureNats = Forall([a, b], InSet(Sub(a, b), Natural), domain=Integers, conditions=[GreaterThanEquals(a, b)])
subtractClosureNats

subtractClosureNatsPos = Forall([a, b], InSet(Sub(a, b), NaturalPos), domain=Integers, conditions=[GreaterThan(a, b)])
subtractClosureNatsPos

subtractComplexClosure = Forall([a, b], InSet(Sub(a, b), Complexes), domain=Complexes)
subtractComplexClosure

subtractRealClosure = Forall([a, b], InSet(Sub(a, b), Reals), domain=Reals)
subtractRealClosure

subtractOneInNats = Forall(a, InSet(Sub(a, one), Natural), domain=NaturalPos)
subtractOneInNats

diffNotEqZero = Forall((a, b), NotEquals(Sub(a, b), zero), domain=Complexes, conditions=[NotEquals(a, b)])
diffNotEqZero

subtractAsAddNeg = Forall([x, y], Equals(Sub(x, y), 
                                         Add(x, Neg(y))), 
                          domain=Complexes)
subtractAsAddNeg

addNegAsSubtract = Forall([x, y], Equals(Add(x, Neg(y)),
                                         Sub(x, y)), 
                          domain=Complexes)
addNegAsSubtract


absorbTermsIntoSubtraction = Forall([wEtc, x, y, zEtc],
                                    Equals(Add(wEtc, Sub(x, y), zEtc),
                                           Sub(Add(wEtc, x, zEtc), y)), domain=Complexes)
absorbTermsIntoSubtraction


subtractCancelElimSums = Forall([x, y, z], 
                        Equals(Sub(Add(x, y), Add(x, z)),
                              Sub(y, z)), domain=Complexes)
subtractCancelElimSums

subtractCancelElimLeftSum = Forall([w, x, yEtc, zEtc], 
                        Equals(Sub(Add(w, x), Add(yEtc, w, zEtc)),
                              Sub(x, Add(yEtc, zEtc))), domain=Complexes)
subtractCancelElimLeftSum

subtractCancelElimRightSum = Forall([wEtc, x, yEtc, z], 
                        Equals(Sub(Add(wEtc, x, yEtc), Add(x, z)),
                              Sub(Add(wEtc, yEtc), z)), domain=Complexes)
subtractCancelElimRightSum

subtractCancelTwoSums = Forall([vEtc, w, xEtc, yEtc, zEtc], 
                        Equals(Sub(Add(vEtc, w, xEtc), Add(yEtc, w, zEtc)),
                              Sub(Add(vEtc, xEtc), Add(yEtc, zEtc))), domain=Complexes)
subtractCancelTwoSums

subtractCancelLeftSum = Forall([xEtc, y, zEtc], 
                        Equals(Sub(Add(xEtc, y, zEtc), y),
                               Add(xEtc, zEtc)), domain=Complexes)
subtractCancelLeftSum

subtractCancelRightSum = Forall([xEtc, y, zEtc], 
                        Equals(Sub(y, Add(xEtc, y, zEtc)),
                               Neg(Add(xEtc, zEtc))), domain=Complexes)
subtractCancelRightSum

subtractCancelRightSumSingleRight = Forall([x, y], Equals(Sub(y, Add(y, x)), Neg(x)), domain=Complexes)
subtractCancelRightSumSingleRight

subtractCancelRightSumSingleLeft = Forall([x, y], Equals(Sub(y, Add(x, y)), Neg(x)), domain=Complexes)
subtractCancelRightSumSingleLeft

subtractCancelLeftSumSingleRight = Forall([x, y], Equals(Sub(Add(y, x), y), x), domain=Complexes)
subtractCancelLeftSumSingleRight

subtractCancelLeftSumSingleLeft = Forall([x, y], Equals(Sub(Add(x, y), y), x), domain=Complexes)
subtractCancelLeftSumSingleLeft

subtractCancelComplete = Forall(x, Equals(Sub(x, x), zero), domain=Complexes)
subtractCancelComplete

distributeSubtraction = Forall([x, yEtc],
                              Equals(Sub(x, Add(yEtc)),
                                    Add(x, Etcetera(Neg(yMulti)))),
                              domain=Complexes)
distributeSubtraction

cancelAddition = Forall([a,b],
                        Equals(Add(a, Sub(b,b)), a),
                       domain=Complexes)
cancelAddition

cancelSubAndAdd = Forall([a,b],
                         Equals(Sub(Sub(a,Neg(b)), b), a),
                        domain=Complexes)
cancelSubAndAdd

cancelSubThenAdd = Forall([a,b],
                        Equals(Add(Sub(a,b), b), a),
                       domain=Complexes)
cancelSubThenAdd

convertAddNegToSub = Forall([a,b],
                            Equals(Add(a,Neg(b)), Sub(a,b)),
                            domain=Complexes)
convertAddNegToSub

endTheorems(locals(), __package__)
