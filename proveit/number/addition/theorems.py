from proveit.logic import Forall, InSet, Equals
from proveit.number import Integers, Naturals, NaturalsPos, Reals, RealsPos, RealsNeg, Complexes
from proveit.number import Add, GreaterThan, LessThan
from proveit.common import a, b, x, aEtc, cEtc, xEtc, yEtc, zEtc, vEtc, wEtc
from proveit.number.common import zero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

addIntClosure = Forall([xEtc], InSet(Add(xEtc),Integers), domain = Integers)
addIntClosure

addNatClosure = Forall((a, b), InSet(Add(a, b), Naturals), domain=Naturals)
addNatClosure

addRealClosure = Forall([xEtc], InSet(Add(xEtc),Reals), domain=Reals)
addRealClosure

addComplexClosure = Forall([xEtc], InSet(Add(xEtc),Complexes), domain = Complexes)
addComplexClosure

addNatPosClosure = Forall((aEtc, b, cEtc), InSet(Add(aEtc, b, cEtc), NaturalsPos), domain=Naturals, conditions=[GreaterThan(b, zero)])
addNatPosClosure

addZero = Forall(x, Equals(Add(zero, x), x), domain=Complexes)
addZero

addComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Add(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Add(vEtc,yEtc,xEtc,wEtc,zEtc)
                        ),
                 domain = Complexes
                 )
addComm

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
                                                          domain=Reals),
                                     domain=RealsPos)
strictlyIncreasingAdditions


# In[80]:

# One issue with this is that it only applies when |aEtc|+|bEtc| > 0.  This isn't an issue
# for applying the theorem because there will be an error if b is left alone with Add, but
# it will be an issue when deriving this.  Probably need to include |aEtc|+|bEtc| > 0 as a condition.
strictlyDecreasingAdditions = Forall((aEtc, cEtc), Forall(b, LessThan(Add(aEtc, b, cEtc), b),
                                                          domain=Reals),
                                     domain=RealsNeg)
strictlyDecreasingAdditions



endTheorems(locals(), __package__)
