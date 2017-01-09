from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.number import Integers, NaturalsPos, Reals, RealsPos, Complexes
from proveit.number import Divide, Fraction, Add, Sub, Sum, Mult, Exp
from proveit.common import a, b, c, n, w, x, y, z, P, S, xMulti, wEtc, xEtc, yEtc, zEtc, PyEtc
from proveit.number.common import zero, one, ComplexesSansZero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

divideRealClosure = Forall([a, b], InSet(Divide(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
divideRealClosure       

divideRealPosClosure = Forall([a, b], InSet(Divide(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
divideRealPosClosure

fractionRealClosure = Forall([a, b], InSet(Fraction(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
fractionRealClosure   

fractionPosClosure = Forall([a, b], InSet(Fraction(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
fractionPosClosure

divideComplexClosure = Forall([a, b], InSet(Divide(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
divideComplexClosure       

fractionComplexClosure = Forall([a, b], InSet(Fraction(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
fractionComplexClosure          

divideNotEqZero = Forall([a, b], NotEquals(Divide(a,b), zero), domain=ComplexesSansZero)
divideNotEqZero

fractionNotEqZero = Forall([a, b], NotEquals(Fraction(a,b), zero), domain=ComplexesSansZero)
fractionNotEqZero

fracZeroNumer = Forall(x, Equals(Fraction(zero, x), zero), domain=Complexes)
fracZeroNumer

fracOneDenom = Forall(x, Equals(Fraction(x, one), x), domain=Complexes)
fracOneDenom

distributeFractionThroughSum = Forall([xEtc, y], 
                                      Equals(Fraction(Add(xEtc), y),
                                             Add(Etcetera(Fraction(xMulti, y)))), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributeFractionThroughSum

distributeFractionThroughSumRev = Forall([xEtc, y], 
                                      Equals(Add(Etcetera(Fraction(xMulti, y))),
                                             Fraction(Add(xEtc), y)), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributeFractionThroughSumRev

distributeFractionThroughSubtract = Forall([x, y, z], 
                                          Equals(Fraction(Sub(x, y), z),
                                                 Sub(Fraction(x, z), Fraction(y, z))), 
                                          domain=Complexes, conditions=[NotEquals(z, zero)])
distributeFractionThroughSubtract

distributeFractionThroughSubtractRev = Forall([x, y, z], 
                                              Equals(Sub(Fraction(x, z), Fraction(y, z)),
                                                     Fraction(Sub(x, y), z)), 
                                              domain=Complexes, conditions=[NotEquals(z, zero)])
distributeFractionThroughSubtractRev

distributeFractionThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(Fraction(Sum(yEtc, PyEtc, domain=S), z),
                                                          Sum(yEtc, Fraction(PyEtc, z), domain=S)),
                                                  domain=Complexes)))
distributeFractionThroughSummation

distributeFractionThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(Sum(yEtc, Fraction(PyEtc, z), domain=S),
                                                         Fraction(Sum(yEtc, PyEtc, domain=S), z)),
                                                  domain=Complexes)))
distributeFractionThroughSummationRev

fracInProd = Forall([wEtc, x, y, zEtc], Equals(Mult(wEtc, Fraction(x, y), zEtc),
                                        Fraction(Mult(wEtc, x, zEtc), y)), domain=Complexes)
fracInProd

fracInProdRev = Forall([wEtc, x, y, zEtc], 
                       Equals(Fraction(Mult(wEtc, x, zEtc), y),
                             Mult(wEtc, Fraction(x, y), zEtc)), domain=Complexes)
fracInProdRev

prodOfFracs = Forall([x, y, z, w], Equals(Mult(Fraction(x, z), Fraction(y, w)),
                                           Fraction(Mult(x, y), Mult(z, w))), domain=Complexes)
prodOfFracs

prodOfFracsRev = Forall([x, y, z, w], Equals(Fraction(Mult(x, y), Mult(z, w)),
                                          Mult(Fraction(x, z), Fraction(y, w))), domain=Complexes)
prodOfFracsRev

prodOfFracsLeftNumerOne = Forall([x, y, z], Equals(Mult(Fraction(one, y), Fraction(x, z)),
                                                 Fraction(x, Mult(y, z))), domain=Complexes)
prodOfFracsLeftNumerOne

prodOfFracsLeftNumerOneRev = Forall([x, y, z], Equals(Fraction(x, Mult(y, z)),
                                                   Mult(Fraction(one, y), Fraction(x, z))), domain=Complexes)
prodOfFracsLeftNumerOneRev

prodOfFracsRightNumerOne = Forall([x, y, z], Equals(Mult(Fraction(x, y), Fraction(one, z)),
                                                 Fraction(x, Mult(y, z))), domain=Complexes)
prodOfFracsRightNumerOne

prodOfFracsRightNumerOneRev = Forall([x, y, z], Equals(Fraction(x, Mult(y, z)),
                                                    Mult(Fraction(x, y), Fraction(one, z))), domain=Complexes)
prodOfFracsRightNumerOneRev

fracCancelLeft = Forall([x,y,z],
                   Equals(Fraction(Mult(x,y),Mult(x,z)),
                         Fraction(y,z)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelLeft

fracCancelDenomLeft = Forall([x,y],
                             Equals(Fraction(Mult(x,y),x),
                                    y),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelDenomLeft

fracCancelNumerLeft = Forall([x,y],
                             Equals(Fraction(x,Mult(x,y)),
                                    Fraction(one,y)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelNumerLeft

multFracLeftCancel = Forall([x,y],
                      Equals(Mult(Fraction(x,y),y),x),
                      domain = Complexes, conditions = [NotEquals(y, zero)])
multFracLeftCancel

multFracRightCancel = Forall([x,y],
                             Equals(Mult(x, Fraction(y, x)),y),
                             domain = Complexes, conditions = [NotEquals(x, zero)])
multFracRightCancel

fracCancelComplete = Forall(x, Equals(Fraction(x, x), one), 
                            domain=Complexes, conditions = [NotEquals(x, zero)])
fracCancelComplete

reverseFractionOfSubtractions = Forall([w, x, y, z], Equals(Fraction(Sub(w, x), Sub(y, z)),
                                                           Fraction(Sub(x, w), Sub(z, y))), domain=Complexes)
reverseFractionOfSubtractions

fracIntExp = Forall(n, Forall((a, b), 
                              Equals(Fraction(Exp(a, n), Exp(b, n)),
                                     Exp(Fraction(a, b), n)),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integers)
fracIntExp

fracIntExpRev = Forall(n, Forall((a, b), 
                                 Equals(Exp(Fraction(a, b), n),
                                        Fraction(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integers)
fracIntExpRev

fracNatPosExp = Forall(n, Forall((a, b), 
                              Equals(Fraction(Exp(a, n), Exp(b, n)),
                                     Exp(Fraction(a, b), n)),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalsPos)
fracNatPosExp

fracNatPosExpRev = Forall(n, Forall((a, b), 
                              Equals(Exp(Fraction(a, b), n),
                                     Fraction(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalsPos)
fracNatPosExpRev

endTheorems(locals(), __package__)
