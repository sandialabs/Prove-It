
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, NotExists, BOOLEANS, TRUE, FALSE, inBool, Not, And, Or, Implies, Iff, Equals, NotEquals
from proveit.common import A, B, C, P, Q, R, S, x, y, PofA, Qetc, Retc, xEtc, yEtc, zEtc, PxEtc, PyEtc, PxyEtc, etc_QxEtc, etc_QyEtc, etc_RyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems


# In[2]:

# In[3]:
beginTheorems(locals())

notFalse = Not(FALSE)
notFalse


# In[4]:

trueAndTrue = And(TRUE, TRUE)
trueAndTrue


# In[5]:

trueOrTrue = Or(TRUE, TRUE)
trueOrTrue


# In[6]:

trueOrFalse = Or(TRUE, FALSE)
trueOrFalse


# In[7]:

falseOrTrue = Or(FALSE, TRUE)
falseOrTrue


# In[8]:

trueEqTrue = Equals(TRUE, TRUE)
trueEqTrue


# In[9]:

falseEqFalse = Equals(FALSE, FALSE)
falseEqFalse


# In[10]:

eqTrueRevIntro = Forall(A, Implies(A, Equals(TRUE, A)))
eqTrueRevIntro


# In[11]:

eqTrueRevElim = Forall(A, Implies(Equals(TRUE, A), A))
eqTrueRevElim


# In[12]:

notImpliesEqFalse = Forall(A, Implies(Not(A), Equals(A, FALSE)))
notImpliesEqFalse


# In[13]:

notImpliesEqFalseRev = Forall(A, Implies(Not(A), Equals(FALSE, A)))
notImpliesEqFalseRev


# In[14]:

fromDoubleNegation = Forall(A, Implies(Not(Not(A)), A))
fromDoubleNegation


# In[15]:

trueConclusion = Forall(A, Implies(A, TRUE))
trueConclusion


# In[16]:

selfImplication = Forall(A, Implies(A, A))
selfImplication


# In[17]:

impliesTT = Equals(Implies(TRUE, TRUE), TRUE)
impliesTT


# In[18]:

impliesFT = Equals(Implies(FALSE, TRUE), TRUE)
impliesFT


# In[19]:

impliesFF = Equals(Implies(FALSE, FALSE), TRUE)
impliesFF


# In[20]:

iffTT = Equals(Iff(TRUE, TRUE), TRUE)
iffTT


# In[21]:

iffFF = Equals(Iff(FALSE, FALSE), TRUE)
iffFF


# In[22]:

iffTF = Equals(Iff(TRUE, FALSE), FALSE)
iffTF


# In[23]:

iffFT = Equals(Iff(FALSE, TRUE), FALSE)
iffFT


# In[24]:

iffImpliesRight = Forall((A, B), Implies(Iff(A, B), Implies(A, B)))
iffImpliesRight


# In[25]:

iffImpliesLeft = Forall((A, B), Implies(Iff(A, B), Implies(B, A)))
iffImpliesLeft


# In[26]:

iffSymmetry = Forall((A, B), Implies(Iff(A, B), Iff(B, A)))
iffSymmetry


# In[27]:

iffTransitivity = Forall((A, B, C), Implies(And(Iff(A, B), Iff(B, C)), Iff(A, C)))
iffTransitivity


# In[28]:

notTimpliesF = Implies(Not(TRUE), FALSE)
notTimpliesF


# In[29]:

conjunctionIntro = Forall((A, B), And(A, B), conditions=(A, B))
conjunctionIntro


# In[30]:

unfoldInBool = Forall(A, Implies(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))
unfoldInBool


# In[31]:

foldInBool = Forall(A, Implies(Or(Equals(A, TRUE), Equals(A, FALSE)), inBool(A)))
foldInBool


# In[32]:

contradictionFromNegation = Forall(A, Implies(Not(A), Implies(A, FALSE)))
contradictionFromNegation


# In[33]:

notFromEqFalse = Forall(A, Implies(Equals(A, FALSE), Not(A)))
notFromEqFalse


# In[34]:

notFromEqFalseRev = Forall(A, Implies(Equals(FALSE, A), Not(A)))
notFromEqFalseRev


# In[35]:

notOrFromNeither = Forall((A, B), Implies(Not(A), Implies(Not(B), Not(Or(A, B)))))
notOrFromNeither


# In[36]:

orContradiction = Forall((A, B), Implies(Or(A, B), FALSE), conditions=(Not(A), Not(B)))
orContradiction


# In[37]:

orImpliesLeftIfNotRight = Forall((A, B), Implies(Or(A, B), A), conditions=(inBool(A), Not(B)))
orImpliesLeftIfNotRight


# In[38]:

orImpliesRightIfNotLeft = Forall((A, B), Implies(Or(A, B), B), conditions=(Not(A), inBool(B)))
orImpliesRightIfNotLeft


# In[39]:

doubleNegation = Forall(A, Implies(A, Not(Not(A))))
doubleNegation


# In[40]:

eqFalseFromNegation = Forall(A, Implies(A, Equals(Not(A), FALSE)))
eqFalseFromNegation


# In[41]:

eqFalseRevFromNegation = Forall(A, Implies(A, Equals(FALSE, Not(A))))
eqFalseRevFromNegation


# In[42]:

fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), domain=BOOLEANS)
fromNotFalse


# In[43]:

transpositionFromNegated = Forall((A, B), Implies(Implies(Not(B), Not(A)), Implies(A, B)), conditions=inBool(B))
transpositionFromNegated


# In[44]:

doubleNegateConclusion = Forall((A, B), Implies(Implies(A, B), Implies(A, Not(Not(B)))), conditions=inBool(B))
doubleNegateConclusion


# In[45]:

transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), domain=BOOLEANS)
transpositionFromNegatedHypothesis


# In[46]:

transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), conditions=inBool(B))
transpositionFromNegatedConclusion


# In[47]:

transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), domain=BOOLEANS)
transpositionToNegated


# In[48]:

trueNotFalse = NotEquals(TRUE, FALSE)
trueNotFalse


# In[49]:

notEqualsFalse = Forall(A, Implies(A, NotEquals(A, FALSE)))
notEqualsFalse


# In[50]:

trueInBool = inBool(TRUE)
trueInBool


# In[51]:

falseInBool = inBool(FALSE)
falseInBool


# In[52]:

unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, domain=BOOLEANS), And(PofTrue, PofFalse)))
unfoldForallOverBool


# In[53]:

inBoolIfEqTrue = Forall(A, Implies(Equals(A, TRUE), inBool(A)))
inBoolIfEqTrue


# In[54]:

inBoolIfEqTrueRev = Forall(A, Implies(Equals(TRUE, A), inBool(A)))
inBoolIfEqTrueRev


# In[55]:

inBoolIfEqFalse = Forall(A, Implies(Equals(A, FALSE), inBool(A)))
inBoolIfEqFalse


# In[56]:

inBoolIfEqFalseRev = Forall(A, Implies(Equals(FALSE, A), inBool(A)))
inBoolIfEqFalseRev


# In[57]:

hypotheticalDisjunction = Forall((A, B, C), Implies(And(Implies(A, C), Implies(B, C)), Implies(Or(A, B), C)), domain=BOOLEANS)
hypotheticalDisjunction


# In[58]:

foldForallOverBool = Forall(P, Implies(And(PofTrue, PofFalse), Forall(A, PofA, domain = BOOLEANS)))
foldForallOverBool


# In[59]:

forallBoolEvalTrue = Forall(P, Implies(And(PofTrue, PofFalse), Equals(Forall(A, PofA, domain=BOOLEANS), TRUE)))
forallBoolEvalTrue


# In[60]:

forallBundling = Forall((P, Qetc, Retc, S), Implies(Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc), Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc))))
forallBundling


# In[61]:

forallUnraveling = Forall((P, Qetc, Retc, S), Implies(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallUnraveling


# In[62]:

iffOverBoolImplEq = Forall((A, B), Implies(Iff(A, B), Equals(A, B)), domain=BOOLEANS)
iffOverBoolImplEq


# In[63]:

doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=BOOLEANS)
doubleNegationEquiv


# In[64]:

forallBundledEquiv = Forall((P, Qetc, Retc, S), Equals(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallBundledEquiv


# In[65]:

forallEqTrueEquiv = Forall((P, Qetc, S), Equals(Forall(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, Equals(PxEtc, TRUE), S, etc_QxEtc)))
forallEqTrueEquiv


# In[66]:

implicationClosure = Forall((A, B), inBool(Implies(A, B)), domain=BOOLEANS)
implicationClosure


# In[67]:

iffClosure = Forall((A, B), inBool(Iff(A, B)), domain=BOOLEANS)
iffClosure


# In[68]:

conjunctionClosure = Forall((A, B), inBool(And(A, B)), domain=BOOLEANS)
conjunctionClosure


# In[69]:

disjunctionClosure = Forall((A, B), inBool(Or(A, B)), domain=BOOLEANS)
disjunctionClosure


# In[70]:

negationClosure = Forall(A, inBool(Not(A)), domain=BOOLEANS)
negationClosure


# In[71]:

hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=BOOLEANS)
hypotheticalContradiction


# In[72]:

existsDefNegation = Forall((P, Qetc, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc)))
existsDefNegation


# In[73]:

notExistsUnfolding = Forall((P, Qetc, S), Implies(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))
notExistsUnfolding


# In[74]:

notExistsFolding = Forall((P, Qetc, S), Implies(Not(Exists(xEtc, PxEtc, S, etc_QxEtc)), NotExists(xEtc, PxEtc, S, etc_QxEtc)))
notExistsFolding


# In[75]:

existsInBool = Forall((P, Qetc, S), inBool(Exists(xEtc, PxEtc, S, etc_QxEtc)))
existsInBool


# In[76]:

existenceByExample = Forall((P, Qetc, S), Forall(xEtc, Implies(PxEtc, Exists(yEtc, PyEtc, S, etc_QyEtc)), S, etc_QxEtc))
existenceByExample


# In[77]:

existsNotImpliesNotForall = Forall((P, Qetc, S), Implies(Exists(xEtc, Not(PxEtc), S, etc_QxEtc), Not(Forall(xEtc, PxEtc, S, etc_QxEtc))))
existsNotImpliesNotForall


# In[78]:

forallImpliesNotExistsNot = Forall((P, Qetc, S), Implies(Forall(xEtc, PxEtc, S, etc_QxEtc), NotExists(xEtc, Not(PxEtc), S, etc_QxEtc)))
forallImpliesNotExistsNot


# In[79]:

def _forallBoolEvalFalse(PofTrueVal, PofFalseVal):
    return Forall(P, Implies(And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal)), 
                             Equals(Forall(A, PofA, domain=BOOLEANS), FALSE)))


# In[80]:

forallBoolEvalFalseViaFF = _forallBoolEvalFalse(FALSE, FALSE)
forallBoolEvalFalseViaFF


# In[81]:

forallBoolEvalFalseViaFT = _forallBoolEvalFalse(FALSE, TRUE)
forallBoolEvalFalseViaFT


# In[82]:

forallBoolEvalFalseViaTF = _forallBoolEvalFalse(TRUE, FALSE)
forallBoolEvalFalseViaTF


# In[83]:

orIfAny = Forall((xEtc, y, zEtc), Implies(y, Or(xEtc, y, zEtc)), domain=BOOLEANS)
orIfAny

endTheorems(locals(), __package__)




