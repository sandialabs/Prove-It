
# coding: utf-8

# In[1]:

from proveit.basiclogic.boolean.boolOps import Implies, Not, Or
from proveit.basiclogic import Equals
from proveit.basiclogic.boolean.quantifiers import Forall
from proveit.common import a, b, c, x, y, z, f, fx, fy, fa, fb, xEtc, yEtc, zEtc
from proveit.number.arithmeticOps import Add, Subtract, Multiply, GreaterThan, LessThan,     GreaterThanEquals, LessThanEquals, Summation, DiscreteContiguousSet
from proveit.number.numberSets import Integers
from proveit.number.common import one
from proveit import beginAxioms, endAxioms

beginAxioms(locals())


# Here we define the addition operation to be associative.  Don't use this ADD for any non-associative operation.

# In[3]:

addAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Add(
                                xEtc,yEtc,zEtc),
                        Add(
                                xEtc,Add(yEtc),zEtc)
                        ),
                  )
addAssoc


# Here we define the addition operation to be associative.  Don't use this ADD for any non-associative operation.

# In[4]:

multAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Multiply(
                                xEtc,yEtc,zEtc),
                        Multiply(
                                xEtc,Multiply(yEtc),zEtc)
                        )
                  )
multAssoc


# In[5]:

reverseGreaterThanEquals = Forall((x, y), Implies(GreaterThanEquals(x, y), LessThanEquals(y, x)))
reverseGreaterThanEquals


# In[6]:

reverseLessThanEquals = Forall((x, y), Implies(LessThanEquals(x, y), GreaterThanEquals(y, x)))
reverseLessThanEquals


# In[7]:

reverseGreaterThan = Forall((x, y), Implies(GreaterThan(x, y), LessThan(y, x)))
reverseGreaterThan


# In[8]:

reverseLessThan = Forall((x, y), Implies(LessThan(x, y), GreaterThan(y, x)))
reverseLessThan


# In[9]:

greaterThanEqualsDef = Forall((x,y), Implies(GreaterThanEquals(x,y), Or(GreaterThan(x,y),Equals(x,y))))
greaterThanEqualsDef


# In[10]:

lessThanEqualsDef = Forall((x,y), Implies(LessThanEquals(x,y), Or(LessThan(x,y),Equals(x,y))))
lessThanEqualsDef


# In[11]:

lessThanTransLessThanRight = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThan(y,z),
                                             LessThan(x,z))))
lessThanTransLessThanRight


# In[12]:

lessThanTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThanEquals(y,z),
                                             LessThan(x,z))))
lessThanTransLessThanEqualsRight


# In[13]:

lessThanTransLessThanLeft = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThan(z,x),
                                             LessThan(z,y))))
lessThanTransLessThanLeft


# In[14]:

lessThanTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThanEquals(z,x),
                                             LessThan(z,y))))
lessThanTransLessThanEqualsLeft


# In[15]:

lessThanEqualsTransLessThanRight = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThan(y,z),
                                             LessThan(x,z))))
lessThanEqualsTransLessThanRight


# In[16]:

lessThanEqualsTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThanEquals(y,z),
                                             LessThanEquals(x,z))))
lessThanEqualsTransLessThanEqualsRight


# In[17]:

lessThanEqualsTransLessThanLeft = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThan(z,x),
                                             LessThan(z,y))))
lessThanEqualsTransLessThanLeft


# In[18]:

lessThanEqualsTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThanEquals(z,x),
                                             LessThanEquals(z,y))))
lessThanEqualsTransLessThanEqualsLeft


# In[19]:

greaterThanTransGreaterThanRight = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThan(y,z),
                                                  GreaterThan(x,z))))
greaterThanTransGreaterThanRight


# In[20]:

greaterThanTransGreaterThanEqualsRight = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThanEquals(y,z),
                                                  GreaterThan(x,z))))
greaterThanTransGreaterThanEqualsRight


# In[21]:

greaterThanTransGreaterThanLeft = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThan(z,x),
                                                  GreaterThan(z,y))))
greaterThanTransGreaterThanLeft


# In[22]:

greaterThanTransGreaterThanEqualsLeft = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThanEquals(z,x),
                                                  GreaterThan(z,y))))
greaterThanTransGreaterThanEqualsLeft


# In[23]:

greaterThanEqualsTransGreaterThanRight = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThan(y,z),
                                                             GreaterThan(x,z))))
greaterThanEqualsTransGreaterThanRight


# In[24]:

greaterThanEqualsTransGreaterThanEqualsRight = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThanEquals(y,z),
                                                             GreaterThanEquals(x,z))))
greaterThanEqualsTransGreaterThanEqualsRight


# In[25]:

greaterThanEqualsTransGreaterThanLeft = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThan(z,x),
                                                             GreaterThan(z,y))))
greaterThanEqualsTransGreaterThanLeft


# In[26]:

greaterThanEqualsTransGreaterThanEqualsLeft = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThanEquals(z,x),
                                                             GreaterThanEquals(z,y))))
greaterThanEqualsTransGreaterThanEqualsLeft


# These define summation over a discrete continguous set.  Does not assume that addition is commutative or associative.

# In[27]:

sumSingle = Forall(f, Forall(a,
                              Equals(Summation(x,fx,DiscreteContiguousSet(a,a)),
                                     fa),
                              domain=Integers))
sumSingle


# In[28]:

sumSplitLast = Forall(f, 
                      Forall([a,b],
                             Equals(Summation(x,fx,DiscreteContiguousSet(a,b)),
                                    Add(Summation(x,fx,DiscreteContiguousSet(a,Subtract(b, one))),
                                       fb)),
                             domain=Integers, conditions=[LessThan(a, b)]))
sumSplitLast


# In[29]:

endAxioms(locals(), __package__)
# In[ ]:



