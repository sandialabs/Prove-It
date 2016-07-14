
# coding: utf-8

# In[1]:

from proveit.expression import Operation
from proveit.basiclogic import In, Implies, Forall, Exists, Equals, SetOfAll
from proveit.number import Summation, Multiply, Exponentiate, DiscreteContiguousSet,     Fraction, Subtract, Add, LessThan, LessThanEquals, Mod
from proveit.common import  a, b, c, f, g, k, l, m, x, y, z, fx, fa, fb, gy, A, N, R, S, Am, xEtc, yEtc, zEtc
from proveit.number.numberSets import Integers, Reals, Complexes
from proveit.number.common import zero, one, two, infinity
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


# In[3]:

addAssocRev = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Add(
                                xEtc,Add(yEtc),zEtc),
                        Add(
                                xEtc,yEtc,zEtc)
                        )
                  )
addAssocRev


# In[4]:

multAssocRev = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Multiply(
                                xEtc,Multiply(yEtc),zEtc),
                        Multiply(
                                xEtc,yEtc,zEtc)
                        )
                  )
multAssocRev


# In[5]:

powOneUnchanged = Forall([a], Equals(Exponentiate(a, one), a))
powOneUnchanged


# In[6]:

endTheorems(locals(), __package__)

# In[ ]:



