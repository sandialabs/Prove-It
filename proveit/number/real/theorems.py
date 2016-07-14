
# coding: utf-8

# In[1]:

from proveit import Lambda
from proveit.logic import InSet, NotInSet, And, Iff, BOOLEANS
from proveit.logic import Forall, Exists, Equals, NotEquals
from proveit.number.common import *
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Divide, Fraction, Abs, Exponentiate, Sqrt, Neg
from proveit.number.arithmeticOps import Min, Max, IntervalOO, IntervalCO, IntervalOC, IntervalCC, Summation, Integrate
from proveit.number.roundingOps import Round, Ceil, Floor
from proveit.number.moduloOp import Mod, ModAbs
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

# In[3]:

relaxGreaterThan = Forall([a,b],
                         GreaterThanEquals(a,b),
                         domain = Reals,
                         conditions = GreaterThan(a,b))
relaxGreaterThan


# In[4]:

relaxLessThan = Forall([a,b],
                         LessThanEquals(a,b),
                         domain = Reals,
                         conditions = LessThan(a,b))
relaxLessThan


# In[5]:

lessThanInBools = Forall([a, b], InSet(LessThan(a, b), BOOLEANS), domain=Reals)
lessThanInBools


# In[6]:

lessThanEqualsInBools = Forall([a, b], InSet(LessThanEquals(a, b), BOOLEANS), domain=Reals)
lessThanEqualsInBools


# In[7]:

greaterThanInBools = Forall([a, b], InSet(GreaterThan(a, b), BOOLEANS), domain=Reals)
greaterThanInBools


# In[8]:

greaterThanEqualsInBools = Forall([a, b], InSet(GreaterThanEquals(a, b), BOOLEANS), domain=Reals)
greaterThanEqualsInBools


# In[9]:

inComplexes = Forall(a,
                    InSet(a,Complexes),
                    domain = Reals)
inComplexes


# In[10]:

inRealsPos_inReals = Forall(a, InSet(a,Reals), domain = RealsPos)
inRealsPos_inReals


# In[11]:

inRealsNeg_inReals = Forall(a, InSet(a,Reals), domain = RealsNeg)
inRealsNeg_inReals


# In[12]:

inRealsPos_inComplexes = Forall(a, InSet(a,Complexes), domain = RealsPos)
inRealsPos_inComplexes


# In[13]:

inRealsNeg_inComplexes = Forall(a, InSet(a,Complexes), domain = RealsNeg)
inRealsNeg_inComplexes


# In[14]:

inRealsPos_iff_positive = Forall(a, Iff(InSet(a, RealsPos), GreaterThan(a, zero)), domain=Reals)
inRealsPos_iff_positive


# In[15]:

inRealsNeg_iff_negative = Forall(a, Iff(InSet(a, RealsNeg), LessThan(a, zero)), domain=Reals)
inRealsNeg_iff_negative


# In[16]:

positive_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[GreaterThan(a, zero)])
positive_implies_notZero


# In[17]:

negative_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[LessThan(a, zero)])
negative_implies_notZero


# In[18]:

allInIntervalOO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOO(a, b)), domain=Reals)
allInIntervalOO_InReals 


# In[19]:

allInIntervalCO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCO(a, b)), domain=Reals)
allInIntervalCO_InReals 


# In[20]:

allInIntervalOC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOC(a, b)), domain=Reals)
allInIntervalOC_InReals 


# In[21]:

allInIntervalCC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCC(a, b)), domain=Reals)
allInIntervalCC_InReals 


# In[22]:

intervalOOLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOO(a, b)), domain=Reals)
intervalOOLowerBound


# In[23]:

intervalOOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalOO(a, b)), domain=Reals)
intervalOOUpperBound


# In[24]:

intervalCOLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCO(a, b)), domain=Reals)
intervalCOLowerBound


# In[25]:

intervalCOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalCO(a, b)), domain=Reals)
intervalCOUpperBound


# In[26]:

intervalOCLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOC(a, b)), domain=Reals)
intervalOCLowerBound


# In[27]:

intervalOCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalOC(a, b)), domain=Reals)
intervalOCUpperBound


# In[28]:

intervalCCLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCC(a, b)), domain=Reals)
intervalCCLowerBound


# In[29]:

intervalCCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalCC(a, b)), domain=Reals)
intervalCCUpperBound


# In[30]:

inIntervalOO = Forall((a, b, x), InSet(x, IntervalOO(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThan(x, b)])
inIntervalOO


# In[31]:

inIntervalCO = Forall((a, b, x), InSet(x, IntervalCO(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThan(x, b)])
inIntervalCO


# In[32]:

inIntervalOC = Forall((a, b, x), InSet(x, IntervalOC(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThanEquals(x, b)])
inIntervalOC


# In[33]:

inIntervalCC = Forall((a, b, x), InSet(x, IntervalCC(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThanEquals(x, b)])
inIntervalCC


# In[34]:

rescaleInIntervalOO = Forall((a, b, c), Forall(x, InSet(Multiply(c, x), IntervalOO(Multiply(c, a), Multiply(c, b))), 
                                               domain=IntervalOO(a, b)), domain=Reals)
rescaleInIntervalOO


# In[35]:

rescaleInIntervalOC = Forall((a, b, c), Forall(x, InSet(Multiply(c, x), IntervalOC(Multiply(c, a), Multiply(c, b))), 
                                               domain=IntervalOC(a, b)), domain=Reals)
rescaleInIntervalOC


# In[36]:

rescaleInIntervalCO = Forall((a, b, c), Forall(x, InSet(Multiply(c, x), IntervalCO(Multiply(c, a), Multiply(c, b))), 
                                               domain=IntervalCO(a, b)), domain=Reals)
rescaleInIntervalCO


# In[37]:

rescaleInIntervalCC = Forall((a, b, c), Forall(x, InSet(Multiply(c, x), IntervalCC(Multiply(c, a), Multiply(c, b))), 
                                               domain=IntervalCC(a, b)), domain=Reals)
rescaleInIntervalCC


# In[38]:

relaxIntervalCO = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalCO(a, b)), domain=Reals)
relaxIntervalCO


# In[39]:

relaxIntervalOC = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalOC(a, b)), domain=Reals)
relaxIntervalOC


# In[40]:

relaxIntervalOOleft = Forall((a, b), Forall(x, InSet(x, IntervalCO(a, b)), 
                                            domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOleft


# In[41]:

relaxIntervalOOright = Forall((a, b), Forall(x, InSet(x, IntervalOC(a, b)), 
                                             domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOright


# In[42]:

notIntIfBetweenSuccessiveInts = Forall(n, Forall(x, NotInSet(x, Integers), domain=IntervalOO(n, Add(n, one))), domain=Integers)
notIntIfBetweenSuccessiveInts


# In[43]:

addClosure = Forall([xEtc], InSet(Add(xEtc),Reals), domain=Reals)
addClosure


# In[44]:

subtractClosure = Forall([a, b], InSet(Subtract(a, b), Reals), domain=Reals)
subtractClosure


# In[45]:

negClosure = Forall(a, InSet(Neg(a), Reals), domain=Reals)
negClosure


# In[46]:

negatedPositiveIsNegative = Forall(a, LessThan(Neg(a), zero), domain=Reals, conditions=[GreaterThan(a, zero)])
negatedPositiveIsNegative


# In[47]:

negatedNegativeIsPositive = Forall(a, GreaterThan(Neg(a), zero), domain=Reals, conditions=[LessThan(a, zero)])
negatedNegativeIsPositive


# In[48]:

multClosure = Forall([xEtc], InSet(Multiply(xEtc),Reals), domain=Reals)
multClosure


# In[49]:

multPosClosure = Forall([xEtc], InSet(Multiply(xEtc),RealsPos), domain=RealsPos)
multPosClosure


# In[50]:

divideClosure = Forall([a, b], InSet(Divide(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
divideClosure       


# In[51]:

dividePosClosure = Forall([a, b], InSet(Divide(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
dividePosClosure


# In[52]:

fractionClosure = Forall([a, b], InSet(Fraction(a, b), Reals), domain=Reals, conditions=[NotEquals(b, zero)])
fractionClosure   


# In[53]:

fractionPosClosure = Forall([a, b], InSet(Fraction(a, b), RealsPos), domain=RealsPos, conditions=[NotEquals(b, zero)])
fractionPosClosure


# In[54]:

powClosure = Forall([a, b], InSet(Exponentiate(a, b), Reals), domain=Reals,
                       conditions=[GreaterThanEquals(a, zero), GreaterThan(b, zero)])
powClosure


# In[55]:

powPosClosure = Forall([a, b], InSet(Exponentiate(a, b), RealsPos), domain=Reals,
                       conditions=[GreaterThan(a, zero)])
powPosClosure


# In[56]:

sqrtClosure = Forall([a], InSet(Sqrt(a), Reals), domain=Reals,
                       conditions=[GreaterThanEquals(a, zero)])
sqrtClosure


# In[57]:

sqrtPosClosure = Forall([a], InSet(Sqrt(a), RealsPos), domain=RealsPos)
sqrtPosClosure


# Should generalize to even power closure, but need to define and implement evens set to do this.

# In[58]:

sqrdClosure = Forall(a, InSet(Exponentiate(a, two), RealsPos), 
                     domain=Reals, conditions=[NotEquals(a, zero)])
sqrdClosure


# In[59]:

minClosure = Forall((a, b), InSet(Min(a, b), Reals), domain=Reals)
minClosure


# In[60]:

minPosClosure = Forall((a, b), InSet(Min(a, b), RealsPos), domain=RealsPos)
minPosClosure


# In[61]:

maxClosure = Forall((a, b), InSet(Max(a, b), Reals), domain=Reals)
maxClosure


# In[62]:

maxPosClosure = Forall((a, b), InSet(Max(a, b), RealsPos), domain=RealsPos)
maxPosClosure


# In[63]:

roundClosure = Forall(a, InSet(Round(a), Integers), domain=Reals)
roundClosure


# In[64]:

roundNatClosure = Forall(a, InSet(Round(a), Naturals), domain=RealsPos)
roundNatClosure


# In[65]:

ceilClosure = Forall(a, InSet(Ceil(a), Integers), domain=Reals)
ceilClosure


# In[66]:

ceilNatPosClosure = Forall(a, InSet(Ceil(a), NaturalsPos), domain=RealsPos)
ceilNatPosClosure


# In[67]:

floorClosure = Forall(a, InSet(Floor(a), Integers), domain=Reals)
floorClosure


# In[68]:

floorNatClosure = Forall(a, InSet(Floor(a), Naturals), domain=RealsPos)
floorNatClosure


# In[69]:

modClosure = Forall((a, b), InSet(Mod(a, b), Reals), domain=Reals)
modClosure


# In[70]:

modAbsClosure = Forall((a, b), InSet(ModAbs(a, b), Reals), domain=Reals)
modAbsClosure


# In[71]:

summationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Reals), domain=S), 
                                          InSet(Summation(xEtc, PxEtc, domain=S), Reals)))
summationClosure


# In[72]:

integrationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Reals), domain=S), 
                                            InSet(Integrate(xEtc, PxEtc, domain=S), Reals)))
integrationClosure


# In[73]:

modInIntervalCO = Forall((a, b), InSet(Mod(a, b), IntervalCO(zero, b)), domain=Reals)
modInIntervalCO


# In[74]:

sqrtOfProd = Forall(xEtc, Equals(Sqrt(Multiply(xEtc)),
                              Multiply(Etcetera(Sqrt(xMulti)))),
                  domain=RealsPos)
sqrtOfProd


# In[75]:

prodOfSqrts = Forall(xEtc, Equals(Multiply(Etcetera(Sqrt(xMulti))),
                                  Sqrt(Multiply(xEtc))),
                     domain=RealsPos)
prodOfSqrts


# In[76]:

sqrtTimesItself = Forall(x, Equals(Multiply(Sqrt(x), Sqrt(x)), x),
                         domain=Reals, conditions=[GreaterThanEquals(x, zero)])
sqrtTimesItself


# In[77]:

absElim = Forall(x, Equals(Abs(x), x), domain=Reals, conditions=[GreaterThanEquals(x, zero)])
absElim


# In[78]:

absIneq = Forall((x, y), Iff(LessThanEquals(Abs(x), y), And(LessThanEquals(Neg(y), x), LessThanEquals(x, y))),
                 domain = Reals, conditions=[GreaterThanEquals(y, zero)])
absIneq


# In[79]:

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


# In[81]:

notEqualsIsLessThanOrGreaterThan = Forall((a, x), Or(LessThan(x, a), GreaterThan(x, a)), domain=Reals, conditions=[NotEquals(x, a)])
notEqualsIsLessThanOrGreaterThan


# In[82]:

eInRealsPos = InSet(e,RealsPos)
eInRealsPos


# In[83]:

eNotZero = NotEquals(e,zero)
eNotZero


# In[84]:

piInRealsPos = InSet(pi,RealsPos)
piInRealsPos


# In[85]:

piNotZero = NotEquals(pi, zero)
piNotZero


# In[86]:

modAbsScaled = Forall((a, b, c), Equals(Multiply(a, ModAbs(b, c)), ModAbs(Multiply(a, b), Multiply(a, c))), domain=Reals)
modAbsScaled


# In[87]:

modAbsSubtractCancel = Forall((a, b, c), LessThanEquals(ModAbs(Subtract(Mod(Add(b, a), c), b), c), 
                                                        Abs(a)),
                              domain=Reals)
modAbsSubtractCancel


# In[88]:

divIneqThm1 = Forall([a,b,c],
                    LessThanEquals(Fraction(a,b),Fraction(c,b)),
                    domain=Reals,
                    conditions=(LessThanEquals(a,c),GreaterThan(b,zero))
                    )
divIneqThm1


# In[89]:

divIneqThm1strong = Forall([a,b,c],
                    LessThan(Fraction(a,b),Fraction(c,b)),
                    domain=Reals,
                    conditions=(LessThan(a,c),GreaterThan(b,zero))
                    )
divIneqThm1strong


# In[90]:

divIneqThm1cor = Forall([a,b,c],
                    LessThanEquals(Multiply(b,a),Multiply(b,c)),
                    domain=Reals,
                    conditions=(LessThanEquals(a,c),GreaterThan(b,zero))
                    )
divIneqThm1cor


# In[91]:

divIneqThm2 = Forall([a,b,c],
                    LessThanEquals(Fraction(a,b),Fraction(a,c)),
                    domain=Reals,
                    conditions=(
                                GreaterThanEquals(b,c),
                                GreaterThanEquals(a,zero),
                                GreaterThan(b,zero),
                                GreaterThan(c,zero)
                                )
                    )
divIneqThm2


# In[92]:

squarePosIneq = Forall([a,b],
                        LessThanEquals(Exponentiate(Abs(a),two),Exponentiate(b,two)),
                        domain = Reals,
                        conditions = (LessThanEquals(Abs(a),b),))
squarePosIneq


# In[93]:

squarePosEq = Forall(a,
                     Equals(Exponentiate(Abs(a),two),Exponentiate(a,two)),
                     domain = Reals)
squarePosEq


# In[94]:

absPos = Forall(a,
               Equals(Abs(a),a),
               domain = RealsPos)
#               conditions = (GreaterThanEquals(a,zero)))
absPos


# In[95]:

absTwoPi = InSet(Multiply(two,pi),RealsPos)
absTwoPi


# In[96]:

lessThanEqualsAddRight = Forall([a, b, c], LessThanEquals(Add(a, c), Add(b, c)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddRight


# In[97]:

lessThanEqualsAddLeft = Forall([a, b, c], LessThanEquals(Add(c, a), Add(c, b)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsAddLeft


# In[98]:

lessThanEqualsSubtract = Forall([a, b, c], LessThanEquals(Subtract(a, c), Subtract(b, c)), domain=Reals, conditions=[LessThanEquals(a, b)])
lessThanEqualsSubtract


# In[99]:

sumIneq2 = Forall([a,b,c,d],
                  Implies(And(LessThanEquals(a,c), LessThanEquals(b,d)), LessThanEquals(Add(a,b),Add(c,d))),
                 domain=Reals)
sumIneq2


# In[100]:

lessThanAddRight = Forall([a, b, c], LessThan(Add(a, c), Add(b, c)), domain=Reals, conditions=[LessThan(a, b)])
lessThanAddRight


# In[101]:

lessThanAddLeft = Forall([a, b, c], LessThan(Add(c, a), Add(c, b)), domain=Reals, conditions=[LessThan(a, b)])
lessThanAddLeft


# In[102]:

lessThanSubtract = Forall([a, b, c], LessThan(Subtract(a, c), Subtract(b, c)), domain=Reals, conditions=[LessThan(a, b)])
lessThanSubtract


# In[103]:

greaterThanEqualsAddRight = Forall([a, b, c], GreaterThanEquals(Add(a, c), Add(b, c)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddRight


# In[104]:

greaterThanEqualsAddLeft = Forall([a, b, c], GreaterThanEquals(Add(c, a), Add(c, b)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsAddLeft


# In[105]:

greaterThanEqualsSubtract = Forall([a, b, c], GreaterThanEquals(Subtract(a, c), Subtract(b, c)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
greaterThanEqualsSubtract


# In[106]:

greaterThanAddRight = Forall([a, b, c], GreaterThan(Add(a, c), Add(b, c)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanAddRight


# In[107]:

greaterThanAddLeft = Forall([a, b, c], GreaterThan(Add(c, a), Add(c, b)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanAddLeft


# In[108]:

greaterThanSubtract = Forall([a, b, c], GreaterThan(Subtract(a, c), Subtract(b, c)), domain=Reals, conditions=[GreaterThan(a, b)])
greaterThanSubtract


# In[109]:

negatedLessThan = Forall([a, b], GreaterThan(Neg(a), Neg(b)), domain=Reals, conditions=[LessThan(a, b)])
negatedLessThan


# In[110]:

negatedLessThanEquals = Forall([a, b], GreaterThanEquals(Neg(a), Neg(b)), domain=Reals, conditions=[LessThanEquals(a, b)])
negatedLessThanEquals


# In[111]:

negatedGreaterThan = Forall([a, b], LessThan(Neg(a), Neg(b)), domain=Reals, conditions=[GreaterThan(a, b)])
negatedGreaterThan


# In[112]:

negatedGreaterThanEquals = Forall([a, b], LessThanEquals(Neg(a), Neg(b)), domain=Reals, conditions=[GreaterThanEquals(a, b)])
negatedGreaterThanEquals


# In[113]:

ineqThm5 = Forall([a,b,c],
                  GreaterThanEquals(Multiply(c,a),Multiply(c,b)),
                  domain = Reals,
                  conditions = (GreaterThan(c,zero),GreaterThanEquals(a,b)))
ineqThm5


# In[114]:

powIneq = Forall([a, b, c], GreaterThanEquals(Exponentiate(a, b), Exponentiate(a, c)), 
                 domain=Reals, conditions= (GreaterThanEquals(a, one), GreaterThanEquals(b, c)))
powIneq


# In[115]:

ineqThm6 = Forall([a,b],
                  GreaterThanEquals(Add(a,b),a),
                  domain = Reals,
                  conditions = GreaterThanEquals(b,zero))
ineqThm6


# In[116]:

ineqThm6a = Forall([a,b],
                  LessThanEquals(Add(a,b),a),
                  domain = Reals,
                  conditions = LessThanEquals(b,zero))
ineqThm6a


# In[117]:

ineqThm7 = Forall([x,l],
                  LessThanEquals(
                                Fraction(one,Exponentiate(Subtract(l,x),two)),
                                Fraction(one,Exponentiate(l,two))
                                ),
                  domain = Reals,
                  conditions = (LessThanEquals(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm7


# In[118]:

ineqThm7a = Forall([x],
                   Forall([a],
                       Forall([l],
                          LessThanEquals(
                                        Multiply(a,Fraction(one,Exponentiate(Subtract(l,x),two))),
                                        Multiply(a,Fraction(one,Exponentiate(l,two)))
                                        ),
                          domain=Integers,
                          conditions = LessThanEquals(l,zero)),
                        domain=Reals,
                        conditions=GreaterThanEquals(a,zero)),                
                   domain = Reals,
                   conditions = (LessThanEquals(zero,x),
                                 LessThanEquals(x,one)))
ineqThm7a


# In[119]:

ineqThm8 = Forall([x,l],
                  LessThanEquals(
                                Fraction(one,Exponentiate(Subtract(l,x),two)),
                                Fraction(one,Exponentiate(Subtract(l,one),two)),
                                ),
                  domain = Reals,
                  conditions = (GreaterThan(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm8


# In[120]:

ineqThm8a = Forall([x],
                Forall([a],
                   Forall([l],
                              LessThanEquals(
                                            Multiply(a,Fraction(one,Exponentiate(Subtract(l,x),two))),
                                            Multiply(a,Fraction(one,Exponentiate(Subtract(l,one),two))),
                                            ),
                              domain = Integers,
                              conditions = GreaterThan(l,zero)),
                        domain=Reals,
                        conditions=GreaterThanEquals(a,zero)),
                   domain = Reals, 
                   conditions = (LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm8a


# In[121]:

ineqThm9 = Forall(theta,LessThanEquals(Abs(Subtract(one,Exponentiate(e,Multiply(i,theta)))),two),domain = Reals)
ineqThm9


# In[122]:

ineqThm10 =  Forall([w,x,y,z],LessThanEquals(w,Fraction(x,z)),
                    domain = Reals,
                    conditions = (LessThanEquals(w,Fraction(x,y)),
                                  GreaterThanEquals(y,z),
                                  GreaterThan(w,zero),
                                  GreaterThan(x,zero),
                                  GreaterThan(y,zero),
                                  GreaterThan(z,zero)))
ineqThm10


# In[123]:

ineqThm10a =  Forall([w,x,y,z],LessThanEquals(w,Fraction(x,z)),
                    domain = Reals,
                    conditions = (LessThanEquals(w,Fraction(x,y)),
                                  GreaterThanEquals(y,z),
                                  GreaterThanEquals(w,zero),
                                  GreaterThan(x,zero),
                                  GreaterThan(y,zero),
                                  GreaterThan(z,zero)))
ineqThm10a


# In[124]:

boundedSum = Forall((S, f, g), Implies(Forall(x, LessThanEquals(fx, gx), domain=S), 
                                     LessThanEquals(Summation(x, fx, domain=S),
                                               Summation(x, gx, domain=S))))
boundedSum


# In[125]:

sumFactor_temp = Forall([a,b,c], Equals(Add(Multiply(a,b), Multiply(a,c)), Multiply(a, Add(b,c))), domain=Reals)
sumFactor_temp


# In[126]:

simplifyQuarterTimesTwo = Equals(Multiply(Fraction(one,four), two), Fraction(one,two))
simplifyQuarterTimesTwo


# In[127]:

boundedInvSqrdIntegral = Forall([a, b], LessThanEquals(Integrate(l, Fraction(one,Exponentiate(l,two)), 
                                                                 IntervalCC(a, b)),
                                                       Fraction(one, a)),
                                domain=RealsPos, conditions=[LessThanEquals(a, b)])
boundedInvSqrdIntegral   


# In[128]:

inverseSqrdIsEvenFunc = InSet(Lambda(l, Fraction(one, Exponentiate(l, two))), EvenFuncs)
inverseSqrdIsEvenFunc


# In[129]:

inverseSqrdIsMonDecFunc = InSet(Lambda(l, Fraction(one, Exponentiate(l, two))), MonDecFuncs)
inverseSqrdIsMonDecFunc


# In[130]:

endTheorems(locals(), __package__)



