
# coding: utf-8

# In[1]:

from proveit.logic import Equals, NotEquals, Implies, Not, And, Forall, TRUE, FALSE, inBool
from proveit.common import A, a, b, c, x, y, z, f, P, fa, fb, fab, fx, fy, fxy, Px, Py, Q
from proveit.logic import Booleans
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

equalsReversal = Forall((x, y), Equals(y, x), conditions=[Equals(x, y)])

lhsSubstitute = Forall((P, x, y), Px, conditions=[Py, Equals(x, y)])

rhsSubstitute = Forall((P, x, y), Py, conditions=[Px, Equals(x, y)])

substituteInTrue = Forall((P, x), PofTrue, conditions=[Px, x])

substituteTruth = Forall((P, x), Px, conditions=[PofTrue, x])

substituteInFalse = Forall((P, x), PofFalse, conditions=[Px, Not(x)])

substituteFalsehood = Forall((P, x), Px, conditions=[PofFalse, Not(x)])

rhsViaEquivalence = Forall((P, Q), Q, conditions=[P, Equals(P, Q)])

lhsViaEquivalence = Forall((P, Q), P, conditions=[Q, Equals(P, Q)])

unfoldNotEquals = Forall((x, y), Not(Equals(x, y)), conditions=[NotEquals(x, y)])

foldNotEquals = Forall((x, y), NotEquals(x, y), conditions=[Not(Equals(x, y))])

notEqualsSymmetry = Forall((x, y), NotEquals(y, x), conditions=[NotEquals(x, y)])

notEqualsContradiction = Forall((x, y), FALSE, conditions=[Equals(x, y), NotEquals(x, y)]) 


unaryEvaluation = Forall((f, x, a, c), Implies(Equals(x, a), Implies(Equals(fa, c), Equals(fx, c))))

binarySubstitution = Forall((f, x, y, a, b), Implies(And(Equals(x, a), Equals(y, b)), Equals(fxy, fab)))

binaryEvaluation = Forall((f, x, y, a, b, c), Implies(And(Equals(x, a), Equals(y, b)), Implies(Equals(fab, c), Equals(fxy, c))))

notEqualsInBool = Forall((x, y), inBool(NotEquals(x, y)))

contradictionViaFalsification = Forall(A, FALSE, conditions=[A, Equals(A, FALSE)])

endTheorems(locals(), __package__)
