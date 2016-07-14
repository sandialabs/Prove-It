
# coding: utf-8

# In[1]:

from proveit import Operation
from proveit.logic import Forall, Equals, InSet, NotEquals, And, Or, Implies
from proveit.number import Add, Subtract, Multiply, Exponentiate
from proveit.common import a, b, aEtc, cEtc, f, n, x, y, xEtc, yEtc, P
#from proveit.number.natural.counting import ExprListCount
from proveit.number.numberSets import Integers, Naturals, NaturalsPos, Reals, RealsPos, Complexes
from proveit.number.number import zero, one, two, three, four, five, six, seven, eight, nine
from proveit.number.arithmeticOps import Exponentiate, GreaterThan, GreaterThanEquals, DiscreteContiguousSet,     Summation
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


# In[3]:

inIntegers = Forall(a,InSet(a,Integers),domain = Naturals)
inIntegers


# In[4]:

inReals = Forall(a,InSet(a,Reals),domain = Naturals)
inReals


# In[5]:

inComplexes = Forall(a,InSet(a,Complexes),domain = Naturals)
inComplexes


# In[6]:

inNatPos_inNaturals = Forall(a,InSet(a,Naturals),domain = NaturalsPos)
inNatPos_inNaturals


# In[7]:

inNatPos_inIntegers = Forall(a,InSet(a,Integers),domain = NaturalsPos)
inNatPos_inIntegers


# In[8]:

inNatPos_inRealsPos = Forall(a,InSet(a,RealsPos),domain = NaturalsPos)
inNatPos_inRealsPos


# In[9]:

inNatPos_inReals = Forall(a,InSet(a,Reals),domain = NaturalsPos)
inNatPos_inReals


# In[10]:

inNatPos_inComplexes = Forall(a,InSet(a,Complexes),domain = NaturalsPos)
inNatPos_inComplexes


# In[11]:

naturalsLowerBound = Forall(n, GreaterThanEquals(n, zero), domain=Naturals)
naturalsLowerBound


# In[12]:

naturalsPosLowerBound = Forall(n, GreaterThanEquals(n, one), domain=NaturalsPos)
naturalsPosLowerBound


# In[13]:

allInDiscreteInterval_InNats = Forall((a, b), Forall(n, InSet(n, Naturals), domain=DiscreteContiguousSet(a, b)), domain=Naturals)
allInDiscreteInterval_InNats  


# In[14]:

allInDiscreteInterval_InNatsPos = Forall((a, b), Forall(n, InSet(n, NaturalsPos), domain=DiscreteContiguousSet(a, b)), domain=Integers, conditions=[GreaterThan(a, zero)])
allInDiscreteInterval_InNatsPos


# In[15]:

addClosure = Forall((a, b), InSet(Add(a, b), Naturals), domain=Naturals)
addClosure


# In[16]:

sumInNatsPos = Forall((aEtc, b, cEtc), InSet(Add(aEtc, b, cEtc), NaturalsPos), domain=Naturals, conditions=[GreaterThan(b, zero)])
sumInNatsPos


# In[17]:

subtractOneInNats = Forall(a, InSet(Subtract(a, one), Naturals), domain=NaturalsPos)
subtractOneInNats


# In[18]:

multClosure = Forall((a, b), InSet(Multiply(a, b), Naturals), domain=Naturals)
multClosure


# In[19]:

multPosClosure = Forall((a, b), InSet(Multiply(a, b), NaturalsPos), domain=NaturalsPos)
multPosClosure


# In[20]:

powClosure = Forall((a, b), InSet(Exponentiate(a, b), NaturalsPos), domain=Naturals, conditions=[NotEquals(a, zero)])
powClosure


# In[21]:

subtractOneClosure = Forall(a, InSet(Subtract(a, one), Naturals), domain=NaturalsPos)
subtractOneClosure


# In[22]:

naturalsInduction = Forall(P, Implies(And(Operation(P, zero), 
                                          Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                 domain=Naturals)),
                                      Forall(n, Operation(P, n), domain=Naturals)))
naturalsInduction      


# In[23]:

naturalsPosInduction = Forall(P, Implies(And(Operation(P, one), 
                                             Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                    domain=NaturalsPos)),
                                         Forall(n, Operation(P, n), domain=NaturalsPos)))
naturalsPosInduction 


# In[24]:

#exprListCountSplit = Forall((xEtc, yEtc), Equals(ExprListCount(xEtc, yEtc), Add(ExprListCount(xEtc), ExprListCount(yEtc))))
#exprListCountSplit


# In[25]:

oneInNaturals = InSet(one,Naturals)
oneInNaturals


# In[26]:

twoInNaturals = InSet(two,Naturals)
twoInNaturals


# In[27]:

threeInNaturals = InSet(three,Naturals)
threeInNaturals


# In[28]:

fourInNaturals = InSet(four,Naturals)
fourInNaturals


# In[29]:

fiveInNaturals = InSet(five,Naturals)
fiveInNaturals


# In[30]:

sixInNaturals = InSet(six,Naturals)
sixInNaturals


# In[31]:

sevenInNaturals = InSet(seven,Naturals)
sevenInNaturals


# In[32]:

eightInNaturals = InSet(eight,Naturals)
eightInNaturals


# In[33]:

nineInNaturals = InSet(nine,Naturals)
nineInNaturals


# In[34]:

oneNotZero = NotEquals(one, zero)
oneNotZero


# In[35]:

twoNotZero = NotEquals(two, zero)
twoNotZero


# In[36]:

threeNotZero = NotEquals(three, zero)
threeNotZero


# In[37]:

fourNotZero = NotEquals(four, zero)
fourNotZero


# In[38]:

fiveNotZero = NotEquals(five, zero)
fiveNotZero


# In[39]:

sixNotZero = NotEquals(six, zero)
sixNotZero


# In[40]:

sevenNotZero = NotEquals(seven, zero)
sevenNotZero


# In[41]:

eightNotZero = NotEquals(eight, zero)
eightNotZero


# In[42]:

nineNotZero = NotEquals(nine, zero)
nineNotZero


# In[43]:

twoSquared = Equals(Exponentiate(two,two),four)
twoSquared


# In[44]:

twoSubOne = Equals(Subtract(two, one), one)
twoSubOne


# In[45]:

twoNotZero = NotEquals(two,zero)
twoNotZero


# In[46]:

oneIsPositive = GreaterThan(one,zero)
oneIsPositive


# In[47]:

twoIsPositive = GreaterThan(two,zero)
twoIsPositive


# In[48]:

threeIsPositive = GreaterThan(three,zero)
threeIsPositive


# In[49]:

fourIsPositive = GreaterThan(four,zero)
fourIsPositive


# In[50]:

fiveIsPositive = GreaterThan(five,zero)
fiveIsPositive


# In[51]:

sixIsPositive = GreaterThan(six,zero)
sixIsPositive


# In[52]:

sevenIsPositive = GreaterThan(seven,zero)
sevenIsPositive


# In[53]:

eightIsPositive = GreaterThan(eight,zero)
eightIsPositive


# In[54]:

nineIsPositive = GreaterThan(nine,zero)
nineIsPositive


# In[55]:

oneInNaturalsPos = InSet(one, NaturalsPos)
oneInNaturalsPos


# In[56]:

twoInNaturalsPos = InSet(two, NaturalsPos)
twoInNaturalsPos


# In[57]:

threeInNaturalsPos = InSet(three, NaturalsPos)
threeInNaturalsPos


# In[58]:

fourInNaturalsPos = InSet(four, NaturalsPos)
fourInNaturalsPos


# In[59]:

fiveInNaturalsPos = InSet(five, NaturalsPos)
fiveInNaturalsPos


# In[60]:

sixInNaturalsPos = InSet(six, NaturalsPos)
sixInNaturalsPos


# In[61]:

sevenInNaturalsPos = InSet(seven, NaturalsPos)
sevenInNaturalsPos


# In[62]:

eightInNaturalsPos = InSet(eight, NaturalsPos)
eightInNaturalsPos


# In[63]:

nineInNaturalsPos = InSet(nine, NaturalsPos)
nineInNaturalsPos


# In[64]:

sumZeroAndOne = Forall(f, Equals(Summation(n, Operation(f, n), DiscreteContiguousSet(zero, one)),
                                Add(Operation(f, zero), Operation(f, one))))
sumZeroAndOne


# In[65]:

endTheorems(locals(), __package__)




