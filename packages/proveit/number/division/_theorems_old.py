from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.number import Integer, NaturalPos, Reals, RealsPos, Complexes
from proveit.number import Divide, frac, Add, Sub, Sum, Mult, Exp
from proveit.common import a, b, c, n, w, x, y, z, P, S, xMulti, wEtc, xEtc, yEtc, zEtc, PyEtc
from proveit.number.common import zero, one, ComplexesSansZero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

divideRealClosure = Forall([a, b], InSet(Divide(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
divideRealClosure       

divideRealPosClosure = Forall([a, b], InSet(Divide(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
divideRealPosClosure

fractionRealClosure = Forall([a, b], InSet(frac(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
fractionRealClosure   

fractionPosClosure = Forall([a, b], InSet(frac(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
fractionPosClosure

divideComplexClosure = Forall([a, b], InSet(Divide(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
divideComplexClosure       

fractionComplexClosure = Forall([a, b], InSet(frac(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
fractionComplexClosure          

divideNotEqZero = Forall([a, b], NotEquals(Divide(a,b), zero), domain=ComplexesSansZero)
divideNotEqZero

fractionNotEqZero = Forall([a, b], NotEquals(frac(a,b), zero), domain=ComplexesSansZero)
fractionNotEqZero

fracZeroNumer = Forall(x, Equals(frac(zero, x), zero), domain=Complexes)
fracZeroNumer

fracOneDenom = Forall(x, Equals(frac(x, one), x), domain=Complexes)
fracOneDenom

distributefracThroughSum = Forall([xEtc, y], 
                                      Equals(frac(Add(xEtc), y),
                                             Add(Etcetera(frac(xMulti, y)))), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributefracThroughSum

distributefracThroughSumRev = Forall([xEtc, y], 
                                      Equals(Add(Etcetera(frac(xMulti, y))),
                                             frac(Add(xEtc), y)), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributefracThroughSumRev

distributefracThroughSubtract = Forall([x, y, z], 
                                          Equals(frac(Sub(x, y), z),
                                                 Sub(frac(x, z), frac(y, z))), 
                                          domain=Complexes, conditions=[NotEquals(z, zero)])
distributefracThroughSubtract

distributefracThroughSubtractRev = Forall([x, y, z], 
                                              Equals(Sub(frac(x, z), frac(y, z)),
                                                     frac(Sub(x, y), z)), 
                                              domain=Complexes, conditions=[NotEquals(z, zero)])
distributefracThroughSubtractRev

distributefracThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(frac(Sum(yEtc, PyEtc, domain=S), z),
                                                          Sum(yEtc, frac(PyEtc, z), domain=S)),
                                                  domain=Complexes)))
distributefracThroughSummation

distributefracThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(Sum(yEtc, frac(PyEtc, z), domain=S),
                                                         frac(Sum(yEtc, PyEtc, domain=S), z)),
                                                  domain=Complexes)))
distributefracThroughSummationRev

fracInProd = Forall([wEtc, x, y, zEtc], Equals(Mult(wEtc, frac(x, y), zEtc),
                                        frac(Mult(wEtc, x, zEtc), y)), domain=Complexes)
fracInProd

fracInProdRev = Forall([wEtc, x, y, zEtc], 
                       Equals(frac(Mult(wEtc, x, zEtc), y),
                             Mult(wEtc, frac(x, y), zEtc)), domain=Complexes)
fracInProdRev

prodOfFracs = Forall([x, y, z, w], Equals(Mult(frac(x, z), frac(y, w)),
                                           frac(Mult(x, y), Mult(z, w))), domain=Complexes)
prodOfFracs

prodOfFracsRev = Forall([x, y, z, w], Equals(frac(Mult(x, y), Mult(z, w)),
                                          Mult(frac(x, z), frac(y, w))), domain=Complexes)
prodOfFracsRev

prodOfFracsLeftNumerOne = Forall([x, y, z], Equals(Mult(frac(one, y), frac(x, z)),
                                                 frac(x, Mult(y, z))), domain=Complexes)
prodOfFracsLeftNumerOne

prodOfFracsLeftNumerOneRev = Forall([x, y, z], Equals(frac(x, Mult(y, z)),
                                                   Mult(frac(one, y), frac(x, z))), domain=Complexes)
prodOfFracsLeftNumerOneRev

prodOfFracsRightNumerOne = Forall([x, y, z], Equals(Mult(frac(x, y), frac(one, z)),
                                                 frac(x, Mult(y, z))), domain=Complexes)
prodOfFracsRightNumerOne

prodOfFracsRightNumerOneRev = Forall([x, y, z], Equals(frac(x, Mult(y, z)),
                                                    Mult(frac(x, y), frac(one, z))), domain=Complexes)
prodOfFracsRightNumerOneRev

fracCancelLeft = Forall([x,y,z],
                   Equals(frac(Mult(x,y),Mult(x,z)),
                         frac(y,z)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelLeft

fracCancelDenomLeft = Forall([x,y],
                             Equals(frac(Mult(x,y),x),
                                    y),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelDenomLeft

fracCancelNumerLeft = Forall([x,y],
                             Equals(frac(x,Mult(x,y)),
                                    frac(one,y)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancelNumerLeft

multFracLeftCancel = Forall([x,y],
                      Equals(Mult(frac(x,y),y),x),
                      domain = Complexes, conditions = [NotEquals(y, zero)])
multFracLeftCancel

multFracRightCancel = Forall([x,y],
                             Equals(Mult(x, frac(y, x)),y),
                             domain = Complexes, conditions = [NotEquals(x, zero)])
multFracRightCancel

fracCancelComplete = Forall(x, Equals(frac(x, x), one), 
                            domain=Complexes, conditions = [NotEquals(x, zero)])
fracCancelComplete

reversefracOfSubtractions = Forall([w, x, y, z], Equals(frac(Sub(w, x), Sub(y, z)),
                                                           frac(Sub(x, w), Sub(z, y))), domain=Complexes)
reversefracOfSubtractions

fracIntExp = Forall(n, Forall((a, b), 
                              Equals(frac(Exp(a, n), Exp(b, n)),
                                     Exp(frac(a, b), n)),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integer)
fracIntExp

fracIntExpRev = Forall(n, Forall((a, b), 
                                 Equals(Exp(frac(a, b), n),
                                        frac(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integer)
fracIntExpRev

fracNatPosExp = Forall(n, Forall((a, b), 
                              Equals(frac(Exp(a, n), Exp(b, n)),
                                     Exp(frac(a, b), n)),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalPos)
fracNatPosExp

fracNatPosExpRev = Forall(n, Forall((a, b), 
                              Equals(Exp(frac(a, b), n),
                                     frac(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalPos)
fracNatPosExpRev

endTheorems(locals(), __package__)
