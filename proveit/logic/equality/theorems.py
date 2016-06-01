
# coding: utf-8

# In[1]:

from proveit.logic import Equals, NotEquals, Implies, Not, And, Forall, TRUE, FALSE, inBool
from proveit.common import A, a, b, c, x, y, z, f, P, fa, fb, fab, fx, fy, fxy, Px, Py


# In[3]:

lhsSubstitution = Forall((P, x, y), Implies(Equals(x, y), Implies(Py, Px)))
lhsSubstitution


# In[4]:

rhsSubstitution = Forall((P, x, y), Implies(Equals(x, y), Implies(Px, Py)))
rhsSubstitution


# In[5]:

unaryEvaluation = Forall((f, x, a, c), Implies(Equals(x, a), Implies(Equals(fa, c), Equals(fx, c))))
unaryEvaluation


# In[6]:

binarySubstitution = Forall((f, x, y, a, b), Implies(And(Equals(x, a), Equals(y, b)), Equals(fxy, fab)))
binarySubstitution


# In[7]:

binaryEvaluation = Forall((f, x, y, a, b, c), Implies(And(Equals(x, a), Equals(y, b)), Implies(Equals(fab, c), Equals(fxy, c))))
binaryEvaluation


# In[8]:

unfoldNotEquals = Forall((x, y), Implies(NotEquals(x, y), Not(Equals(x, y))))
unfoldNotEquals


# In[9]:

foldNotEquals = Forall((x, y), Implies(Not(Equals(x, y)), NotEquals(x, y)))
foldNotEquals


# In[10]:

notEqualsSymmetry = Forall((x, y), Implies(NotEquals(x, y), NotEquals(y, x)))
notEqualsSymmetry


# In[11]:

notEqualsInBool = Forall((x, y), inBool(NotEquals(x, y)))
notEqualsInBool


# In[12]:

contradictionFromFalseEquivalence = Forall(A, Implies(Equals(A, FALSE), Implies(A, FALSE)))
contradictionFromFalseEquivalence


# In[13]:

contradictionFromFalseEquivalenceReversed = Forall(A, Implies(Equals(FALSE, A), Implies(A, FALSE)))
contradictionFromFalseEquivalenceReversed



