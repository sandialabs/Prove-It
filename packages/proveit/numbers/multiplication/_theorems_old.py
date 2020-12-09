from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.numbers import Mult, Natural, NaturalPos, Integer, Real, RealPos, Complex, Add, Sub, Sum
from proveit.common import a, b, x, y, P, S, yMulti, vEtc, wEtc, xEtc, yEtc, zEtc, PyEtc
from proveit.numbers.common import zero, one, ComplexSansZero
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

multIntClosure = Forall([xEtc], InSet(Mult(xEtc), Integer), domain=Integer)
multIntClosure

multRealClosure = Forall([xEtc], InSet(Mult(xEtc), Real), domain=Real)
multRealClosure

multRealPosClosure = Forall([xEtc], InSet(Mult(xEtc), RealPos), domain=RealPos)
multRealPosClosure

multComplexClosure = Forall([xEtc], InSet(Mult(xEtc),Complex), domain=Complex)
multComplexClosure

multNotEqZero = Forall([xEtc], NotEquals(Mult(xEtc), zero), domain=ComplexSansZero)
multNotEqZero

multOne = Forall(x, Equals(Mult(one, x), x), domain=Complex)
multOne

multZero = Forall(x, Equals(Mult(zero, x), zero), domain=Complex)
multZero

multComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Mult(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Mult(vEtc,yEtc,xEtc,wEtc,zEtc)
    ),
                 domain = Complex
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
                  domain = Complex
                  )
distributeThroughSum

distributeThroughSumRev =  Forall([xEtc, yEtc, zEtc],
                                  Equals(Add(Etcetera(Mult(xEtc, yMulti, zEtc))),
                                         Mult(xEtc, Add(yEtc), zEtc)),
                                  domain = Complex)
distributeThroughSumRev

distributeThroughSubtract =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Mult(wEtc, Sub(x, y), zEtc),
                        Sub(Mult(wEtc, x, zEtc), Mult(wEtc, y, zEtc))
                        ),
                  domain = Complex
                  )
distributeThroughSubtract

distributeThroughSubtractRev =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Sub(Mult(wEtc, x, zEtc), Mult(wEtc, y, zEtc)),
                        Mult(wEtc, Sub(x, y), zEtc)
                        ),
                  domain = Complex
                  )
distributeThroughSubtractRev

distributeThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complex), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Mult(xEtc, Sum(yEtc, PyEtc, domain=S), zEtc),
                                                          Sum(yEtc, Mult(xEtc, PyEtc, zEtc), domain=S)),
                                                  domain=Complex)))
distributeThroughSummation


distributeThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complex), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Sum(yEtc, Mult(xEtc, PyEtc, zEtc), domain=S),
                                                         Mult(xEtc, Sum(yEtc, PyEtc, domain=S), zEtc)),
                                                  domain=Complex)))
distributeThroughSummationRev

endTheorems(locals(), __package__)
