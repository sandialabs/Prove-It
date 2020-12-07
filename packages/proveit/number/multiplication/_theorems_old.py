from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.number import Mult, Natural, NaturalPos, Integers, Reals, RealsPos, Complexes, Add, Sub, Sum
from proveit.common import a, b, x, y, P, S, yMulti, vEtc, wEtc, xEtc, yEtc, zEtc, PyEtc
from proveit.number.common import zero, one, ComplexesSansZero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

multAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Mult(
                                xEtc,yEtc,zEtc),
                        Mult(
                                xEtc,Mult(yEtc),zEtc)
                        )
                  )
multAssoc

multNatClosure = Forall((a, b), InSet(Mult(a, b), Natural), domain=Natural)
multNatClosure

multNatPosClosure = Forall((a, b), InSet(Mult(a, b), NaturalPos), domain=NaturalPos)
multNatPosClosure

multIntClosure = Forall([xEtc], InSet(Mult(xEtc), Integers), domain=Integers)
multIntClosure

multRealClosure = Forall([xEtc], InSet(Mult(xEtc), Reals), domain=Reals)
multRealClosure

multRealPosClosure = Forall([xEtc], InSet(Mult(xEtc), RealsPos), domain=RealsPos)
multRealPosClosure

multComplexClosure = Forall([xEtc], InSet(Mult(xEtc),Complexes), domain=Complexes)
multComplexClosure

multNotEqZero = Forall([xEtc], NotEquals(Mult(xEtc), zero), domain=ComplexesSansZero)
multNotEqZero

multOne = Forall(x, Equals(Mult(one, x), x), domain=Complexes)
multOne

multZero = Forall(x, Equals(Mult(zero, x), zero), domain=Complexes)
multZero

multComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Mult(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Mult(vEtc,yEtc,xEtc,wEtc,zEtc)
    ),
                 domain = Complexes
                 )
multComm

multAssocRev = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Mult(
                                xEtc,Mult(yEtc),zEtc),
                        Mult(
                                xEtc,yEtc,zEtc)
                        )
                  )
multAssocRev

distributeThroughSum =  Forall([xEtc, yEtc, zEtc],
                  Equals(
                        Mult(xEtc, Add(yEtc), zEtc),
                        Add(Etcetera(Mult(xEtc, yMulti, zEtc)))
                        ),
                  domain = Complexes
                  )
distributeThroughSum

distributeThroughSumRev =  Forall([xEtc, yEtc, zEtc],
                                  Equals(Add(Etcetera(Mult(xEtc, yMulti, zEtc))),
                                         Mult(xEtc, Add(yEtc), zEtc)),
                                  domain = Complexes)
distributeThroughSumRev

distributeThroughSubtract =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Mult(wEtc, Sub(x, y), zEtc),
                        Sub(Mult(wEtc, x, zEtc), Mult(wEtc, y, zEtc))
                        ),
                  domain = Complexes
                  )
distributeThroughSubtract

distributeThroughSubtractRev =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Sub(Mult(wEtc, x, zEtc), Mult(wEtc, y, zEtc)),
                        Mult(wEtc, Sub(x, y), zEtc)
                        ),
                  domain = Complexes
                  )
distributeThroughSubtractRev

distributeThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Mult(xEtc, Sum(yEtc, PyEtc, domain=S), zEtc),
                                                          Sum(yEtc, Mult(xEtc, PyEtc, zEtc), domain=S)),
                                                  domain=Complexes)))
distributeThroughSummation


distributeThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Sum(yEtc, Mult(xEtc, PyEtc, zEtc), domain=S),
                                                         Mult(xEtc, Sum(yEtc, PyEtc, domain=S), zEtc)),
                                                  domain=Complexes)))
distributeThroughSummationRev

endTheorems(locals(), __package__)
