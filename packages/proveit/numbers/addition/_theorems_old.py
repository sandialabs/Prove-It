from proveit.logic import Forall, InSet, Equals
from proveit.numbers import Integer, Natural, NaturalPos, Real, RealPos, RealNeg, Complex
from proveit.numbers import Add, GreaterThan, LessThan
from proveit.common import a, b, x, aEtc, cEtc, xEtc, yEtc, zEtc, vEtc, wEtc
from proveit.numbers.common import zero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

addIntClosure = Forall([xEtc], InSet(Add(xEtc),Integer), domain = Integer)
addIntClosure

addNatClosure = Forall((a, b), InSet(Add(a, b), Natural), domain=Natural)
addNatClosure

addRealClosure = Forall([xEtc], InSet(Add(xEtc),Real), domain=Real)
addRealClosure

addComplexClosure = Forall([xEtc], InSet(Add(xEtc),Complex), domain = Complex)
addComplexClosure

addNatPosClosure = Forall((aEtc, b, cEtc), InSet(Add(aEtc, b, cEtc), NaturalPos), domain=Natural, conditions=[GreaterThan(b, zero)])
addNatPosClosure

addZero = Forall(x, Equals(Add(zero, x), x), domain=Complex)
addZero

addComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Add(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Add(vEtc,yEtc,xEtc,wEtc,zEtc)
                        ),
                 domain = Complex
                 )
addComm

addAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Add(
                                xEtc,yEtc,zEtc),
                        Add(
                                xEtc,Add(yEtc),zEtc)
                        ),
                  )
addAssoc

addAssocRev = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Add(
                                xEtc,Add(yEtc),zEtc),
                        Add(
                                xEtc,yEtc,zEtc)
                        )
                  )
addAssocRev

# One issue with this is that it only applies when |aEtc|+|bEtc| > 0.  This isn't an issue
# for applying the theorem because there will be an error if b is left alone with Add, but
# it will be an issue when deriving this.  Probably need to include |aEtc|+|bEtc| > 0 as a condition.
strictlyIncreasingAdditions = Forall((aEtc, cEtc), Forall(b, GreaterThan(Add(aEtc, b, cEtc), b),
                                                          domain=Real),
                                     domain=RealPos)
strictlyIncreasingAdditions


# In[80]:

# One issue with this is that it only applies when |aEtc|+|bEtc| > 0.  This isn't an issue
# for applying the theorem because there will be an error if b is left alone with Add, but
# it will be an issue when deriving this.  Probably need to include |aEtc|+|bEtc| > 0 as a condition.
strictlyDecreasingAdditions = Forall((aEtc, cEtc), Forall(b, LessThan(Add(aEtc, b, cEtc), b),
                                                          domain=Real),
                                     domain=RealNeg)
strictlyDecreasingAdditions



endTheorems(locals(), __package__)
