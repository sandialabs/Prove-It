from proveit.logic import Equals, Implies, TRUE, FALSE, Iff, Forall, And, Not, inBool, Booleans
from proveit.common import A, B, C
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

impliesTT = Equals(Implies(TRUE, TRUE), TRUE)
impliesTT

impliesFT = Equals(Implies(FALSE, TRUE), TRUE)
impliesFT

impliesFF = Equals(Implies(FALSE, FALSE), TRUE)
impliesFF

iffTT = Equals(Iff(TRUE, TRUE), TRUE)
iffTT

iffFF = Equals(Iff(FALSE, FALSE), TRUE)
iffFF

iffTF = Equals(Iff(TRUE, FALSE), FALSE)
iffTF

iffFT = Equals(Iff(FALSE, TRUE), FALSE)
iffFT

iffImpliesRight = Forall((A, B), Implies(A, B), conditions=[Iff(A, B)])
iffImpliesRight

iffImpliesLeft = Forall((A, B), Implies(B, A), conditions=[Iff(A, B)])
iffImpliesLeft

iffSymmetry = Forall((A, B), Iff(B, A), conditions=[Iff(A, B)])
iffSymmetry

iffTransitivity = Forall((A, B, C), Implies(And(Iff(A, B), Iff(B, C)), Iff(A, C)))
iffTransitivity

transpositionFromNegated = Forall((A, B), Implies(Implies(Not(B), Not(A)), Implies(A, B)), conditions=inBool(B))
transpositionFromNegated

doubleNegateConclusion = Forall((A, B), Implies(Implies(A, B), Implies(A, Not(Not(B)))), conditions=inBool(B))
doubleNegateConclusion

transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), domain=Booleans)
transpositionFromNegatedHypothesis

transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), conditions=inBool(B))
transpositionFromNegatedConclusion

transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), domain=Booleans)
transpositionToNegated

iffOverBoolImplEq = Forall((A, B), Equals(A, B), conditions=[Iff(A, B)], domain=Booleans)
iffOverBoolImplEq

implicationClosure = Forall((A, B), inBool(Implies(A, B)), domain=Booleans)
implicationClosure

iffClosure = Forall((A, B), inBool(Iff(A, B)), domain=Booleans)
iffClosure

endTheorems(locals(), __package__)
