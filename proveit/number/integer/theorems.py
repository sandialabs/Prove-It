
# coding: utf-8

# In[1]:

from proveit.logic import InSet, NotInSet, And, SetOfAll, BOOLEANS
from proveit.logic import Forall, Exists, Equals, Implies
from proveit.number.common import *
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Abs, Exponentiate, Neg, Summation, DiscreteContiguousSet
from proveit.number.arithmeticOps import Integrate, IntervalCC
from proveit.number.moduloOp import Mod
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


# In[3]:

inIntsIsBool = Forall(a, InSet(InSet(a, Integers), BOOLEANS))
inIntsIsBool


# In[4]:

notInIntsIsBool = Forall(a, InSet(NotInSet(a, Integers), BOOLEANS))
notInIntsIsBool


# In[5]:

inReals = Forall(a,InSet(a,Reals),domain=Integers)
inReals


# In[6]:

inComplexes = Forall(a,InSet(a,Complexes),domain=Integers)
inComplexes


# In[7]:

inNaturalsIfNonNeg = Forall(a,InSet(a,Naturals),domain=Integers, conditions=[GreaterThanEquals(a, zero)])
inNaturalsIfNonNeg


# In[8]:

inNaturalsPosIfPos = Forall(a,InSet(a,NaturalsPos),domain=Integers, conditions=[GreaterThan(a, zero)])
inNaturalsPosIfPos


# In[9]:

allInDiscreteInterval_InInts = Forall((a, b), Forall(n, InSet(n, Integers), domain=DiscreteContiguousSet(a, b)), domain=Integers)
allInDiscreteInterval_InInts          


# In[10]:

allInNegativeIntervalAreNegative = Forall((a, b), Forall(n, LessThan(n, zero), domain=DiscreteContiguousSet(a, b)), domain=Integers, conditions=[LessThan(b, zero)])
allInNegativeIntervalAreNegative


# In[11]:

allInPositiveIntervalArePositive = Forall((a, b), Forall(n, GreaterThan(n, zero), domain=DiscreteContiguousSet(a, b)), domain=Integers, conditions=[GreaterThan(a, zero)])
allInPositiveIntervalArePositive


# In[12]:

intervalLowerBound = Forall((a, b), Forall(n, LessThanEquals(a, n), domain=DiscreteContiguousSet(a, b)), domain=Integers)
intervalLowerBound


# In[13]:

intervalUpperBound = Forall((a, b), Forall(n, LessThanEquals(n, b), domain=DiscreteContiguousSet(a, b)), domain=Integers)
intervalUpperBound


# In[14]:

inInterval = Forall((a, b, n), InSet(n, DiscreteContiguousSet(a, b)), domain=Integers, conditions=[LessThanEquals(a, n), LessThanEquals(n, b)])
inInterval


# In[15]:

addClosure = Forall([xEtc], InSet(Add(xEtc),Integers), domain = Integers)
addClosure


# In[16]:

subtractClosure = Forall([a, b], InSet(Subtract(a, b), Integers), domain=Integers)
subtractClosure


# In[17]:

subtractClosureNats = Forall([a, b], InSet(Subtract(a, b), Naturals), domain=Integers, conditions=[GreaterThanEquals(a, b)])
subtractClosureNats


# In[18]:

subtractClosureNatsPos = Forall([a, b], InSet(Subtract(a, b), NaturalsPos), domain=Integers, conditions=[GreaterThan(a, b)])
subtractClosureNatsPos


# In[19]:

negClosure = Forall(a, InSet(Neg(a), Integers), domain=Integers)
negClosure


# In[20]:

multClosure = Forall([xEtc], InSet(Multiply(xEtc),Integers), domain = Integers)
multClosure


# In[21]:

modClosure = Forall((a, b), InSet(Mod(a, b), Integers), domain=Integers)
modClosure


# In[22]:

modInInterval = Forall((a, b), InSet(Mod(a, b), DiscreteContiguousSet(zero, Subtract(b, one))), domain=Integers)
modInInterval


# In[23]:

indexShift = Forall(f,
       Forall([a,b,c],Equals(Summation(x,Operation(f,x),DiscreteContiguousSet(a,b)),
              Summation(x,Operation(f,Subtract(x,c)),DiscreteContiguousSet(Add(a,c),Add(b,c)))),domain=Integers))
indexShift


# In[24]:

shiftLessThanToLessThanEquals = Forall((a, b), LessThanEquals(a, b), domain=Integers, conditions=[LessThan(Subtract(a, one), b)])
shiftLessThanToLessThanEquals


# In[25]:

sumIntegrateIneq1 = Forall(f,
                    Forall([a,b],LessThanEquals(Summation(x,Operation(f,x),DiscreteContiguousSet(a,b)),
                    Add(fa, Integrate(x,Operation(f,x),IntervalCC(a,b)))),
                    domain=Integers,conditions=LessThanEquals(a,b)),
                    domain=MonDecFuncs)
sumIntegrateIneq1


# In[26]:

sumIneq1 = Forall([a,b],
                  Forall([m,n],
                         Implies(Forall(k, 
                                        LessThanEquals(Operation(a,k),Operation(b,k)),
                                        domain=DiscreteContiguousSet(m,n)), 
                                 LessThanEquals(Summation(l,Operation(a,l),DiscreteContiguousSet(m,n)), Summation(l,Operation(b,l),DiscreteContiguousSet(m,n)))
                                 ),
                        domain=Integers))
sumIneq1


# In[28]:

evenFuncSum = Forall(f,
                     Forall([a,b],
                           Equals(Summation(x,Operation(f,x),DiscreteContiguousSet(a,b)),
                                  Summation(x,Operation(f,x),DiscreteContiguousSet(Neg(b),Neg(a)))),
                            domain = Integers),
                    domain = EvenFuncs
                    )
evenFuncSum


# In[29]:

sumEq = Forall([f,g],
                  Forall([m,n],
                         Implies(Forall(k, 
                                        Equals(Operation(f,k),Operation(g,k)),
                                        domain=DiscreteContiguousSet(m,n)), 
                                 Equals(Summation(l,Operation(f,l),DiscreteContiguousSet(m,n)), Summation(l,Operation(g,l),DiscreteContiguousSet(m,n)))
                                 ),
                        domain=Integers))
sumEq


# In[30]:

fullModularRangeEquiv = Forall((N, a, b), 
                               Equals(SetOfAll(x, Mod(x, N), domain=DiscreteContiguousSet(a, b)), 
                                      DiscreteContiguousSet(zero, Subtract(N, one))),
                               domain=Integers, conditions=[Equals(Subtract(b, a), Subtract(N, one))])
fullModularRangeEquiv


# In[31]:

fullModularRangeEquivLeftShift = Forall((N, a, b, c), 
                               Equals(SetOfAll(x, Mod(Add(c, x), N), domain=DiscreteContiguousSet(a, b)), 
                                      DiscreteContiguousSet(zero, Subtract(N, one))),
                               domain=Integers, conditions=[Equals(Subtract(b, a), Subtract(N, one))])
fullModularRangeEquivLeftShift


# In[32]:

fullModularRangeEquivRightShift = Forall((N, a, b, c), 
                               Equals(SetOfAll(x, Mod(Add(x, c), N), domain=DiscreteContiguousSet(a, b)), 
                                      DiscreteContiguousSet(zero, Subtract(N, one))),
                               domain=Integers, conditions=[Equals(Subtract(b, a), Subtract(N, one))])
fullModularRangeEquivRightShift


# In[33]:

sumSplitAfter = Forall(f, Forall([a,b,c],
                            Equals(Summation(x,fx,DiscreteContiguousSet(a,c)),
                                   Add(Summation(x,fx,DiscreteContiguousSet(a,b)),
                                       Summation(x,fx,DiscreteContiguousSet(Add(b,one),c)))),
                                 domain=Integers, conditions=[LessThanEquals(a,b),LessThan(b,c)]))
sumSplitAfter


# In[34]:

sumSplitBefore = Forall(f, Forall([a,b,c],
                            Equals(Summation(x,fx,DiscreteContiguousSet(a,c)),
                                   Add(Summation(x,fx,DiscreteContiguousSet(a,Subtract(b, one))),
                                       Summation(x,fx,DiscreteContiguousSet(b,c)))),
                                  domain=Integers, conditions=[LessThan(a,b),LessThanEquals(b,c)]))
sumSplitBefore


# In[35]:

sumSplitFirst = Forall(f, Forall([a,b],
                                 Equals(Summation(x,fx,DiscreteContiguousSet(a,b)),
                                        Add(fa, Summation(x,fx,DiscreteContiguousSet(Add(a, one),b)))),
                                 domain=Integers, conditions=[LessThan(a,b)]))
sumSplitFirst


# In[36]:


endTheorems(locals(), __package__)

