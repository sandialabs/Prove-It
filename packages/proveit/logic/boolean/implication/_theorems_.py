from proveit.logic import Equals, Implies, TRUE, FALSE, Iff, Forall, And, Not, inBool, Booleans
from proveit.common import A, B, C
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

selfImplication = Forall(A, Implies(A, A))

impliesTT = Equals(Implies(TRUE, TRUE), TRUE)

impliesFT = Equals(Implies(FALSE, TRUE), TRUE)

impliesFF = Equals(Implies(FALSE, FALSE), TRUE)

trueImpliesTrue = Implies(TRUE, TRUE)

falseImpliesTrue = Implies(TRUE, TRUE)

falseImpliesFalse = Implies(FALSE, FALSE)

affirmViaContradiction = Forall(A, Implies(Implies(Not(A), FALSE), A), domain=Booleans)

implicationTransitivity = Forall((A, B, C), Implies(A, C), conditions=[Implies(A, B), Implies(B, C)])

iffTT = Equals(Iff(TRUE, TRUE), TRUE)

iffFF = Equals(Iff(FALSE, FALSE), TRUE)

iffTF = Equals(Iff(TRUE, FALSE), FALSE)

iffFT = Equals(Iff(FALSE, TRUE), FALSE)

trueIffTrue = Iff(TRUE, TRUE)

falseIffFalse = Iff(FALSE, FALSE)

iffImpliesRight = Forall((A, B), Implies(A, B), conditions=[Iff(A, B)])

iffImpliesLeft = Forall((A, B), Implies(B, A), conditions=[Iff(A, B)])

iffSymmetry = Forall((A, B), Iff(B, A), conditions=[Iff(A, B)])

iffTransitivity = Forall((A, B, C), Iff(A, C), conditions=[Iff(A, B), Iff(B, C)])

transpositionFromNegated = Forall((A, B), Implies(Implies(Not(B), Not(A)), Implies(A, B)), conditions=inBool(B))

doubleNegateConclusion = Forall((A, B), Implies(Implies(A, B), Implies(A, Not(Not(B)))), conditions=inBool(B))

transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), domain=Booleans)

transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), conditions=inBool(B))

transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), domain=Booleans)

iffOverBoolImplEq = Forall((A, B), Equals(A, B), conditions=[Iff(A, B)], domain=Booleans)

implicationClosure = Forall((A, B), inBool(Implies(A, B)), domain=Booleans)

iffClosure = Forall((A, B), inBool(Iff(A, B)), domain=Booleans)

endTheorems(locals(), __package__)
