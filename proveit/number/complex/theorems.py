
# coding: utf-8

# In[1]:

from proveit.logic import And, Or, Iff, NotEquals, InSet, Singleton, Difference, SetOfAll
from proveit.logic import Forall, Exists, Equals
from proveit.number.common import *
from proveit.number import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction,     Add, Subtract, Multiply, Divide, Fraction, Abs, Exponentiate, Sqrt, Neg, Summation,     DiscreteContiguousSet
from proveit import Etcetera
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


# In[4]:

iInComplexes = InSet(i, Complexes)
iInComplexes


# In[5]:

iNotZero = NotEquals(i, zero)
iNotZero


# In[6]:

addClosure = Forall([xEtc], InSet(Add(xEtc),Complexes), domain = Complexes)
addClosure


# In[7]:

subtractClosure = Forall([a, b], InSet(Subtract(a, b), Complexes), domain=Complexes)
subtractClosure


# In[8]:

negClosure = Forall(a, InSet(Neg(a), Complexes), domain=Complexes)
negClosure


# In[9]:

multClosure = Forall([xEtc], InSet(Multiply(xEtc),Complexes), domain = Complexes)
multClosure


# In[10]:

divideClosure = Forall([a, b], InSet(Divide(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
divideClosure       


# In[11]:

fractionClosure = Forall([a, b], InSet(Fraction(a, b), Complexes), domain=Complexes, conditions=[NotEquals(b, zero)])
fractionClosure          


# In[12]:

powClosure = Forall([a, b], InSet(Exponentiate(a, b), Complexes), domain=Complexes, 
                    conditions=[NotEquals(a, zero)])
powClosure


# In[13]:

sqrtClosure = Forall([a], InSet(Sqrt(a), Complexes), domain=Complexes)
sqrtClosure


# In[14]:

absClosure = Forall([a], InSet(Abs(a), Reals), domain=Complexes)
absClosure


# In[15]:

absIsNonNeg = Forall(a, GreaterThanEquals(Abs(a), zero), domain=Complexes)
absIsNonNeg


# In[16]:

absPosClosure = Forall([a], InSet(Abs(a), RealsPos), domain=Complexes, conditions=[NotEquals(a, zero)])
absPosClosure


# In[17]:

summationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Complexes), domain=S), 
                                          InSet(Summation(xEtc, PxEtc, domain=S), Complexes)))
summationClosure


# In[18]:

inComplexesSansZero = Forall(a, InSet(a, ComplexesSansZero), 
                             domain=Complexes, conditions=[NotEquals(a, zero)])
inComplexesSansZero


# In[19]:

negNotEqZero = Forall(a, NotEquals(Neg(a), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
negNotEqZero


# In[20]:

diffNotEqZero = Forall((a, b), NotEquals(Subtract(a, b), zero), domain=Complexes, conditions=[NotEquals(a, b)])
diffNotEqZero


# In[21]:

multNotEqZero = Forall([xEtc], NotEquals(Multiply(xEtc), zero), domain=ComplexesSansZero)
multNotEqZero


# In[22]:

divideNotEqZero = Forall([a, b], NotEquals(Divide(a,b), zero), domain=ComplexesSansZero)
divideNotEqZero


# In[23]:

fractionNotEqZero = Forall([a, b], NotEquals(Fraction(a,b), zero), domain=ComplexesSansZero)
fractionNotEqZero


# In[24]:

powNotEqZero = Forall([a, b], NotEquals(Exponentiate(a,b), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
powNotEqZero


# In[25]:

absNotEqZero = Forall([a], NotEquals(Abs(a), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
absNotEqZero


# In[26]:

powZeroEqOne = Forall([a], Equals(Exponentiate(a, zero), one), domain=Complexes, conditions=[NotEquals(a, zero)])
powZeroEqOne


# In[27]:

exponentiatedZero = Forall([x], Equals(Exponentiate(zero, x), zero), domain=Complexes, conditions=[NotEquals(x, zero)])
exponentiatedZero


# In[28]:

exponentiatedOne = Forall([x], Equals(Exponentiate(one, x), one), domain=Complexes)
exponentiatedOne


# In[29]:

multOne = Forall(x, Equals(Multiply(one, x), x), domain=Complexes)
multOne


# In[30]:

multZero = Forall(x, Equals(Multiply(zero, x), zero), domain=Complexes)
multZero


# In[31]:

fracZeroNumer = Forall(x, Equals(Fraction(zero, x), zero), domain=Complexes)
fracZeroNumer


# In[32]:

fracOneDenom = Forall(x, Equals(Fraction(x, one), x), domain=Complexes)
fracOneDenom


# In[33]:

addZero = Forall(x, Equals(Add(zero, x), x), domain=Complexes)
addZero


# In[34]:

triangleInequality = Forall([a,b],
                        LessThanEquals(Abs(Add(a,b)),Add(Abs(a),Abs(b))),
                        domain=Complexes)
triangleInequality


# In[35]:

absProd = Forall(xEtc,
                 Equals(Abs(Multiply(xEtc)),
                        Multiply(Etcetera(Abs(xMulti)))),
                 domain = Complexes)
absProd


# In[36]:

absFrac = Forall([a,b],
                 Equals(Abs(Fraction(a,b)),Fraction(Abs(a),Abs(b))),
                 domain = Complexes)
absFrac


# In[37]:

sumInPow = Forall([a,b,c],
                Equals(Exponentiate(a,Add(b,c)),
                       Multiply(Exponentiate(a,b),Exponentiate(a,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
sumInPow


# In[38]:

sumInPowRev = Forall([a,b,c],
                Equals(Multiply(Exponentiate(a,b),Exponentiate(a,c)),
                       Exponentiate(a,Add(b,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
sumInPowRev


# In[39]:

addOneRightInPow = Forall([a,b],
                Equals(Exponentiate(a,Add(b,one)),
                       Multiply(Exponentiate(a,b),a)),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneRightInPow


# In[40]:

addOneRightInPowRev = Forall([a,b],
                Equals(Multiply(Exponentiate(a,b),a),
                       Exponentiate(a,Add(b,one))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneRightInPowRev


# In[41]:

addOneLeftInPow = Forall([a,b],
                Equals(Exponentiate(a,Add(one, b)),
                       Multiply(a, Exponentiate(a,b))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneLeftInPow


# In[42]:

addOneLeftInPowRev = Forall([a,b],
                Equals(Multiply(a, Exponentiate(a,b)),
                       Exponentiate(a,Add(one, b))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneLeftInPowRev


# In[43]:

diffInPow = Forall([a,b,c],
                Equals(Exponentiate(a,Subtract(b,c)),
                       Multiply(Exponentiate(a,b),Exponentiate(a,Neg(c)))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
diffInPow


# In[44]:

diffInPowRev = Forall([a,b,c],
                Equals(Multiply(Exponentiate(a,b),Exponentiate(a,Neg(c))),
                       Exponentiate(a,Subtract(b,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
diffInPowRev


# In[45]:

diffFracInPow = Forall([a,b,c,d],
                Equals(Exponentiate(a,Subtract(b,Fraction(c, d))),
                       Multiply(Exponentiate(a,b),Exponentiate(a,Fraction(Neg(c), d)))),
                domain = Complexes, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInPow


# In[46]:

diffFracInPowRev = Forall([a,b,c,d],
                Equals(Multiply(Exponentiate(a,b),Exponentiate(a,Fraction(Neg(c), d))),
                       Exponentiate(a,Subtract(b,Fraction(c, d)))),
                domain = Complexes, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInPowRev


# In[47]:

# works because log[a^c b^c] = c log a + c log b
powOfPositivesProd = Forall(c, Forall((a, b),
                             Equals(Exponentiate(Multiply(a,b),c),
                                    Multiply(Exponentiate(a,c),Exponentiate(b,c))),
                             domain=RealsPos),
                domain=Complexes)
powOfPositivesProd


# In[48]:

powOfPositivesProdRev = Forall(c, Forall((a, b),
                             Equals(Multiply(Exponentiate(a,c),Exponentiate(b,c)),
                                   Exponentiate(Multiply(a,b),c)),
                             domain=RealsPos),
                domain=Complexes)
powOfPositivesProdRev


# In[49]:

# Works for integers powers by the commutivity of complex numbers (or their inverses when n < 0).
# Does not work for fractional powers.  Consider sqrt(-1)*sqrt(-1) = -1 not sqrt((-1)*(-1)) = 1.
intPowOfProd = Forall(n, Forall((a, b),
                                Equals(Exponentiate(Multiply(a,b),n),
                                       Multiply(Exponentiate(a,n),Exponentiate(b,n))),
                                domain=Complexes, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                      domain=Integers)
intPowOfProd


# In[50]:

intPowOfProdRev = Forall(n, Forall((a, b),
                                   Equals(Multiply(Exponentiate(a,n),Exponentiate(b,n)),
                                          Exponentiate(Multiply(a,b),n)),
                                   domain=Complexes, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                         domain=Integers)
intPowOfProdRev


# In[51]:

natsPosPowOfProd = Forall(n, Forall((a, b),
                                    Equals(Exponentiate(Multiply(a,b),n),
                                           Multiply(Exponentiate(a,n),Exponentiate(b,n))),
                                    domain=Complexes),
                          domain=NaturalsPos)
natsPosPowOfProd


# In[52]:

natsPosPowOfProdRev = Forall(n, Forall((a, b),
                                       Equals(Multiply(Exponentiate(a,n),Exponentiate(b,n)),
                                              Exponentiate(Multiply(a,b),n)),
                                       domain=Complexes),
                             domain=NaturalsPos)
natsPosPowOfProdRev


# In[53]:

# Works for integers powers through repetition of a^b (or a^{-b}) and adding exponents.
# Does not work for fractional powers.  Consider sqrt[(-1)^2] = 1 not (-1)^{2*(1/2)} = -1.
intPowOfPow = Forall(n, Forall((a, b), 
                            Equals(Exponentiate(Exponentiate(a, b), n), 
                                   Exponentiate(a, Multiply(b, n))), 
                            domain=Complexes, conditions=[NotEquals(a, zero)]), 
                  domain=Integers)
intPowOfPow


# In[54]:

intPowOfNegPow = Forall(n, Forall((a, b), 
                               Equals(Exponentiate(Exponentiate(a, Neg(b)), n), 
                                      Exponentiate(a, Neg(Multiply(b, n)))),
                               domain=Complexes, conditions=[NotEquals(a, zero)]), 
                        domain=Integers)
intPowOfNegPow


# In[55]:

negIntPowOfPow = Forall(n, Forall((a, b),
                            Equals(Exponentiate(Exponentiate(a, b), Neg(n)), 
                                   Exponentiate(a, Neg(Multiply(b, n)))), 
                               domain=Complexes, conditions=[NotEquals(a, zero)]),
                        domain=Integers)

negIntPowOfPow


# In[56]:

negIntPowOfNegPow = Forall(n, Forall((a, b),
                                     Equals(Exponentiate(Exponentiate(a, Neg(b)), Neg(n)), 
                                            Exponentiate(a, Multiply(b, n))), 
                               domain=Complexes, conditions=[NotEquals(a, zero)]),
                           domain=Integers)

negIntPowOfNegPow


# In[57]:

diffSquareComm = Forall([a,b],
                        Equals(
                            Exponentiate(Subtract(a,b),two),
                            Exponentiate(Subtract(b,a),two)),
                        domain = Complexes)
diffSquareComm


# In[58]:

addComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Add(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Add(vEtc,yEtc,xEtc,wEtc,zEtc)
    ),
                 domain = Complexes
                 )
addComm


# In[59]:

subtractAsAddNeg = Forall([x, y], Equals(Subtract(x, y), 
                                         Add(x, Neg(y))), 
                          domain=Complexes)
subtractAsAddNeg


# In[60]:

addNegAsSubtract = Forall([x, y], Equals(Add(x, Neg(y)),
                                         Subtract(x, y)), 
                          domain=Complexes)
addNegAsSubtract


# In[61]:

absorbTermsIntoSubtraction = Forall([wEtc, x, y, zEtc],
                                    Equals(Add(wEtc, Subtract(x, y), zEtc),
                                           Subtract(Add(wEtc, x, zEtc), y)), domain=Complexes)
absorbTermsIntoSubtraction


# In[62]:

subtractCancelElimSums = Forall([x, y, z], 
                        Equals(Subtract(Add(x, y), Add(x, z)),
                              Subtract(y, z)), domain=Complexes)
subtractCancelElimSums


# In[63]:

subtractCancelElimLeftSum = Forall([w, x, yEtc, zEtc], 
                        Equals(Subtract(Add(w, x), Add(yEtc, w, zEtc)),
                              Subtract(x, Add(yEtc, zEtc))), domain=Complexes)
subtractCancelElimLeftSum


# In[64]:

subtractCancelElimRightSum = Forall([wEtc, x, yEtc, z], 
                        Equals(Subtract(Add(wEtc, x, yEtc), Add(x, z)),
                              Subtract(Add(wEtc, yEtc), z)), domain=Complexes)
subtractCancelElimRightSum


# In[65]:

subtractCancelTwoSums = Forall([vEtc, w, xEtc, yEtc, zEtc], 
                        Equals(Subtract(Add(vEtc, w, xEtc), Add(yEtc, w, zEtc)),
                              Subtract(Add(vEtc, xEtc), Add(yEtc, zEtc))), domain=Complexes)
subtractCancelTwoSums


# In[66]:

subtractCancelLeftSum = Forall([xEtc, y, zEtc], 
                        Equals(Subtract(Add(xEtc, y, zEtc), y),
                               Add(xEtc, zEtc)), domain=Complexes)
subtractCancelLeftSum


# In[67]:

subtractCancelRightSum = Forall([xEtc, y, zEtc], 
                        Equals(Subtract(y, Add(xEtc, y, zEtc)),
                               Neg(Add(xEtc, zEtc))), domain=Complexes)
subtractCancelRightSum


# In[68]:

subtractCancelRightSumSingleRight = Forall([x, y], Equals(Subtract(y, Add(y, x)), Neg(x)), domain=Complexes)
subtractCancelRightSumSingleRight


# In[69]:

subtractCancelRightSumSingleLeft = Forall([x, y], Equals(Subtract(y, Add(x, y)), Neg(x)), domain=Complexes)
subtractCancelRightSumSingleLeft


# In[70]:

subtractCancelLeftSumSingleRight = Forall([x, y], Equals(Subtract(Add(y, x), y), x), domain=Complexes)
subtractCancelLeftSumSingleRight


# In[71]:

subtractCancelLeftSumSingleLeft = Forall([x, y], Equals(Subtract(Add(x, y), y), x), domain=Complexes)
subtractCancelLeftSumSingleLeft


# In[72]:

subtractCancelComplete = Forall(x, Equals(Subtract(x, x), zero), domain=Complexes)
subtractCancelComplete


# In[73]:

multComm = Forall([vEtc,wEtc,xEtc,yEtc,zEtc],
                 Equals(
                        Multiply(vEtc,wEtc,xEtc,yEtc,zEtc),
                        Multiply(vEtc,yEtc,xEtc,wEtc,zEtc)
    ),
                 domain = Complexes
                 )
multComm


# In[74]:

distributeThroughSum =  Forall([xEtc, yEtc, zEtc],
                  Equals(
                        Multiply(xEtc, Add(yEtc), zEtc),
                        Add(Etcetera(Multiply(xEtc, yMulti, zEtc)))
                        ),
                  domain = Complexes
                  )
distributeThroughSum


# In[75]:

distributeThroughSumRev =  Forall([xEtc, yEtc, zEtc],
                                  Equals(Add(Etcetera(Multiply(xEtc, yMulti, zEtc))),
                                         Multiply(xEtc, Add(yEtc), zEtc)),
                                  domain = Complexes)
distributeThroughSumRev


# In[76]:

distributeThroughSubtract =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Multiply(wEtc, Subtract(x, y), zEtc),
                        Subtract(Multiply(wEtc, x, zEtc), Multiply(wEtc, y, zEtc))
                        ),
                  domain = Complexes
                  )
distributeThroughSubtract


# In[77]:

distributeThroughSubtractRev =  Forall([wEtc, x, y, zEtc],
                  Equals(
                        Subtract(Multiply(wEtc, x, zEtc), Multiply(wEtc, y, zEtc)),
                        Multiply(wEtc, Subtract(x, y), zEtc)
                        ),
                  domain = Complexes
                  )
distributeThroughSubtractRev


# In[78]:

distributeSubtraction = Forall([x, yEtc],
                              Equals(Subtract(x, Add(yEtc)),
                                    Add(x, Etcetera(Neg(yMulti)))),
                              domain=Complexes)
distributeSubtraction


# In[79]:

distributeNegThroughSum = Forall([xEtc], Equals(Neg(Add(xEtc)),
                                               Add(Etcetera(Neg(xMulti)))),
                                 domain=Complexes)
distributeNegThroughSum


# In[80]:

distributeNegThroughSumRev = Forall([xEtc], 
                                    Equals(Add(Etcetera(Neg(xMulti))),
                                           Neg(Add(xEtc))),
                                 domain=Complexes)
distributeNegThroughSumRev


# In[81]:

distributeNegThroughSubtract = Forall([x, y], Equals(Neg(Subtract(x, y)),
                                               Add(Neg(x), y)),
                                 domain=Complexes)
distributeNegThroughSubtract


# In[82]:

distributeThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Multiply(xEtc, Summation(yEtc, PyEtc, domain=S), zEtc),
                                                          Summation(yEtc, Multiply(xEtc, PyEtc, zEtc), domain=S)),
                                                  domain=Complexes)))
distributeThroughSummation


# In[83]:

distributeThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall([xEtc, zEtc],
                                                   Equals(Summation(yEtc, Multiply(xEtc, PyEtc, zEtc), domain=S),
                                                         Multiply(xEtc, Summation(yEtc, PyEtc, domain=S), zEtc)),
                                                  domain=Complexes)))
distributeThroughSummationRev


# In[84]:

distributeFractionThroughSum = Forall([xEtc, y], 
                                      Equals(Fraction(Add(xEtc), y),
                                             Add(Etcetera(Fraction(xMulti, y)))), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributeFractionThroughSum


# In[85]:

distributeFractionThroughSumRev = Forall([xEtc, y], 
                                      Equals(Add(Etcetera(Fraction(xMulti, y))),
                                             Fraction(Add(xEtc), y)), 
                                      domain=Complexes, conditions=[NotEquals(y, zero)])
distributeFractionThroughSumRev


# In[86]:

distributeFractionThroughSubtract = Forall([x, y, z], 
                                          Equals(Fraction(Subtract(x, y), z),
                                                 Subtract(Fraction(x, z), Fraction(y, z))), 
                                          domain=Complexes, conditions=[NotEquals(z, zero)])
distributeFractionThroughSubtract


# In[87]:

distributeFractionThroughSubtractRev = Forall([x, y, z], 
                                              Equals(Subtract(Fraction(x, z), Fraction(y, z)),
                                                     Fraction(Subtract(x, y), z)), 
                                              domain=Complexes, conditions=[NotEquals(z, zero)])
distributeFractionThroughSubtractRev


# In[88]:

distributeFractionThroughSummation = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(Fraction(Summation(yEtc, PyEtc, domain=S), z),
                                                          Summation(yEtc, Fraction(PyEtc, z), domain=S)),
                                                  domain=Complexes)))
distributeFractionThroughSummation


# In[89]:

distributeFractionThroughSummationRev = Forall([P, S],
                                    Implies(Forall(yEtc, InSet(PyEtc, Complexes), domain=S),
                                            Forall(z,
                                                   Equals(Summation(yEtc, Fraction(PyEtc, z), domain=S),
                                                         Fraction(Summation(yEtc, PyEtc, domain=S), z)),
                                                  domain=Complexes)))
distributeFractionThroughSummationRev


# In[90]:

negTimesPos = Forall([x, y], Equals(Multiply(Neg(x), y), Neg(Multiply(x, y))), domain=Complexes)
negTimesPos


# In[91]:

negTimesPosRev = Forall([x, y], Equals(Neg(Multiply(x, y)), Multiply(Neg(x), y)), domain=Complexes)
negTimesPosRev


# In[92]:

posTimesNeg = Forall([x, y], Equals(Multiply(x, Neg(y)), Neg(Multiply(x, y))), domain=Complexes)
posTimesNeg


# In[93]:

posTimesNegRev = Forall([x, y], Equals(Neg(Multiply(x, y)), Multiply(x, Neg(y))), domain=Complexes)
posTimesNegRev


# In[94]:

negTimesNeg = Forall([x, y], Equals(Multiply(Neg(x), Neg(y)), Multiply(x, y)), domain=Complexes)
negTimesNeg


# In[95]:

fracInProd = Forall([wEtc, x, y, zEtc], Equals(Multiply(wEtc, Fraction(x, y), zEtc),
                                        Fraction(Multiply(wEtc, x, zEtc), y)), domain=Complexes)
fracInProd


# In[96]:

fracInProdRev = Forall([wEtc, x, y, zEtc], 
                       Equals(Fraction(Multiply(wEtc, x, zEtc), y),
                             Multiply(wEtc, Fraction(x, y), zEtc)), domain=Complexes)
fracInProdRev


# In[97]:

prodOfFracs = Forall([x, y, z, w], Equals(Multiply(Fraction(x, z), Fraction(y, w)),
                                           Fraction(Multiply(x, y), Multiply(z, w))), domain=Complexes)
prodOfFracs


# In[98]:

prodOfFracsRev = Forall([x, y, z, w], Equals(Fraction(Multiply(x, y), Multiply(z, w)),
                                          Multiply(Fraction(x, z), Fraction(y, w))), domain=Complexes)
prodOfFracsRev


# In[99]:

prodOfFracsLeftNumerOne = Forall([x, y, z], Equals(Multiply(Fraction(one, y), Fraction(x, z)),
                                                 Fraction(x, Multiply(y, z))), domain=Complexes)
prodOfFracsLeftNumerOne


# In[100]:

prodOfFracsLeftNumerOneRev = Forall([x, y, z], Equals(Fraction(x, Multiply(y, z)),
                                                   Multiply(Fraction(one, y), Fraction(x, z))), domain=Complexes)
prodOfFracsLeftNumerOneRev


# In[101]:

prodOfFracsRightNumerOne = Forall([x, y, z], Equals(Multiply(Fraction(x, y), Fraction(one, z)),
                                                 Fraction(x, Multiply(y, z))), domain=Complexes)
prodOfFracsRightNumerOne


# In[102]:

prodOfFracsRightNumerOneRev = Forall([x, y, z], Equals(Fraction(x, Multiply(y, z)),
                                                    Multiply(Fraction(x, y), Fraction(one, z))), domain=Complexes)
prodOfFracsRightNumerOneRev


# In[103]:

fracCancel1 = Forall([x,y,z],
                   Equals(Fraction(Multiply(x,y),Multiply(x,z)),
                         Fraction(y,z)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancel1


# In[104]:

fracCancel2 = Forall([x,y],
                   Equals(Fraction(Multiply(x,y),x),
                         y),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancel2


# In[105]:

fracCancel3 = Forall([x,y],
                   Equals(Fraction(x,Multiply(x,y)),
                         Fraction(one,y)),domain=Complexes, conditions=[NotEquals(x, zero)])
fracCancel3


# In[106]:

fracCancel4 = Forall([x,y],
                      Equals(Multiply(Fraction(x,y),y),x),
                      domain = Complexes, conditions = [NotEquals(y, zero)])
fracCancel4


# In[107]:

fracCancel5 = Forall([x,y],
                      Equals(Multiply(x, Fraction(y, x)),y),
                      domain = Complexes, conditions = [NotEquals(x, zero)])
fracCancel5


# In[108]:

fracCancelComplete = Forall(x, Equals(Fraction(x, x), one), 
                            domain=Complexes, conditions = [NotEquals(x, zero)])
fracCancelComplete


# In[109]:

reverseFractionOfSubtractions = Forall([w, x, y, z], Equals(Fraction(Subtract(w, x), Subtract(y, z)),
                                                           Fraction(Subtract(x, w), Subtract(z, y))), domain=Complexes)
reverseFractionOfSubtractions


# In[110]:

fracIntExp = Forall(n, Forall((a, b), 
                              Equals(Fraction(Exponentiate(a, n), Exponentiate(b, n)),
                                     Exponentiate(Fraction(a, b), n)),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integers)
fracIntExp


# In[111]:

fracIntExpRev = Forall(n, Forall((a, b), 
                                 Equals(Exponentiate(Fraction(a, b), n),
                                        Fraction(Exponentiate(a, n), Exponentiate(b, n))),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integers)
fracIntExpRev


# In[112]:

fracNatPosExp = Forall(n, Forall((a, b), 
                              Equals(Fraction(Exponentiate(a, n), Exponentiate(b, n)),
                                     Exponentiate(Fraction(a, b), n)),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalsPos)
fracNatPosExp


# In[113]:

fracNatPosExpRev = Forall(n, Forall((a, b), 
                              Equals(Exponentiate(Fraction(a, b), n),
                                     Fraction(Exponentiate(a, n), Exponentiate(b, n))),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalsPos)
fracNatPosExpRev


# In[114]:

oneExp = Forall([x],
               Equals(Exponentiate(x,one),
                      x),
               domain = Complexes)
oneExp


# In[115]:

expOne = Forall([x],
               Equals(Exponentiate(one,x),
                     one),
               domain = Complexes)
expOne


# In[116]:

samePowDistribute = Forall([x,y,z],
                            Equals(Multiply(Exponentiate(x,y),Exponentiate(z,y)),
                                 Exponentiate(Multiply(x,z),y)),
                            domain = Complexes)
samePowDistribute


# In[117]:

cancelAddition = Forall([a,b],
                        Equals(Add(a, Subtract(b,b)), a),
                       domain=Complexes)
cancelAddition


# In[118]:

cancelSubAndAdd = Forall([a,b],
                         Equals(Subtract(Subtract(a,Neg(b)), b), a),
                        domain=Complexes)
cancelSubAndAdd


# In[119]:

cancelSubThenAdd = Forall([a,b],
                        Equals(Add(Subtract(a,b), b), a),
                       domain=Complexes)
cancelSubThenAdd


# In[120]:

negNeg = Forall([a],
                 Equals(Neg(Neg(a)), a),
                domain=Complexes)
negNeg


# In[121]:

negZero = Equals(Neg(zero), zero)
negZero


# In[122]:

cancelAddNeg = Forall([a,b],
                      Equals(Add(Add(a,b),Neg(b)), a),
                      domain=Complexes)
cancelAddNeg


# In[123]:

convertAddNegToSub = Forall([a,b],
                            Equals(Add(a,Neg(b)), Subtract(a,b)),
                            domain=Complexes)
convertAddNegToSub


# In[124]:

# special theorem for expediency
subTwoAddOne = Forall(a, Equals(Add(Subtract(a, two), one),
                               Subtract(a, one)),
                     domain=Complexes)
subTwoAddOne


# In[125]:

# special theorem for expediency
outerCancel = Forall((a, b), Equals(Add(a, Subtract(b, a)),
                                   b),
                    domain=Complexes)
outerCancel


# In[126]:

addTwice = Forall([a],
                  Equals(Add(a,a), Multiply(two, a)),
                 domain=Complexes)
addTwice


# In[127]:

squarePosIneq = Forall([a],
                       Forall([b],
                            LessThanEquals(Exponentiate(Abs(a),two),Exponentiate(b,two)),
                            domain = Reals,
                            conditions = (LessThanEquals(Abs(a),b),)),
                       domain = Complexes)
squarePosIneq


# In[128]:

notEq_iff_diffNotZero = Forall((a, b), Iff(NotEquals(a, b), NotEquals(Subtract(a, b), zero)), domain=Complexes)
notEq_iff_diffNotZero


# In[129]:

infGeomSum = Forall(x,Equals(Summation(m,Exponentiate(x,m),DiscreteContiguousSet(zero,infinity)), 
             Fraction(one,Subtract(one,x))),
              domain=Complexes
              )
infGeomSum


# In[130]:

finGeomSum = Forall([x,k,l],
                Equals(Summation(m,Exponentiate(x,m),DiscreteContiguousSet(k,l)), 
                 Fraction(Subtract(Exponentiate(x,Add(l,one)),Exponentiate(x,k)),Subtract(x,one))),
                 conditions=[InSet(k,Integers),
                  InSet(l,Integers),
                  InSet(x,Complexes),
                  LessThan(k,l)])
finGeomSum


# In[131]:

# Could also make such a theorem to apply whenever addition is communitive, not just Complexes.
equivSums = Forall((f, g, R, S),
                   Implies(Forall(a, InSet(fa, Complexes), domain=R),
                           Equals(Summation(x, fx, domain=R),
                                  Summation(y, Operation(f, gy), domain=S))),
                  conditions=[Equals(SetOfAll(y, gy, domain=S), R)])
equivSums


# In[132]:

endTheorems(locals(), __package__)

