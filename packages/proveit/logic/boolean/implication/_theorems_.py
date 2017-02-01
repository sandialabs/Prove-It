from proveit.logic import Equals, Implies, TRUE, FALSE, Iff, Forall, And, Not, inBool, Booleans
from proveit.common import A, B, C
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

selfImplication = Forall(A, Implies(A, A))

trueImpliesTrue = Implies(TRUE, TRUE)

falseImpliesFalse = Implies(FALSE, FALSE)

falseImpliesTrue = Implies(FALSE, TRUE)

impliesTT = Equals(Implies(TRUE, TRUE), TRUE)

impliesFF = Equals(Implies(FALSE, FALSE), TRUE)

impliesFT = Equals(Implies(FALSE, TRUE), TRUE)

impliesTF = Equals(Implies(TRUE, FALSE), FALSE)

trueImpliesFalseNegated = Not(Implies(TRUE, FALSE))

contradictionElim = Forall(A, A, domain=Booleans, conditions=[Implies(Not(A), FALSE)])

implicationTransitivity = Forall((A, B, C), Implies(A, C), conditions=[Implies(A, B), Implies(B, C)])

trueIffTrue = Iff(TRUE, TRUE)

iffTT = Equals(Iff(TRUE, TRUE), TRUE)

falseIffFalse = Iff(FALSE, FALSE)

iffFF = Equals(Iff(FALSE, FALSE), TRUE)

trueIffFalseNegated = Not(Iff(TRUE, FALSE))

iffTF = Equals(Iff(TRUE, FALSE), FALSE)

falseIffTrueNegated = Not(Iff(FALSE, TRUE))

iffFT = Equals(Iff(FALSE, TRUE), FALSE)

iffImpliesRight = Forall((A, B), Implies(A, B), conditions=[Iff(A, B)])

iffImpliesLeft = Forall((A, B), Implies(B, A), conditions=[Iff(A, B)])

rightFromIff = Forall((A, B), B, conditions=[A, Iff(A, B)])

leftFromIff = Forall((A, B), A, conditions=[Iff(A, B), B])

iffSymmetry = Forall((A, B), Iff(B, A), conditions=[Iff(A, B)])

iffTransitivity = Forall((A, B, C), Iff(A, C), conditions=[Iff(A, B), Iff(B, C)])

affirmViaContradiction = Forall(A, A, domain=Booleans, conditions=[Implies(Not(A), FALSE)])

modusTollensAffirmation = Forall((A, B), A, domain=Booleans, conditions=[Implies(Not(A), B), Not(B)])

denyViaContradiction = Forall(A, Not(A), domain=Booleans, conditions=[Implies(A, FALSE)])



modusTollensDenial = Forall((A, B), Not(A), domain=Booleans, conditions=[Implies(A, B), Not(B)])


fromContraposition = Forall((A, B), Implies(A, B), conditions=[Implies(Not(B), Not(A)), inBool(B)])


toContraposition = Forall((A, B), Implies(Not(B), Not(A)), conditions=[Implies(A, B), inBool(A)])





transpositionFromNegated = Forall((A, B), Implies(A, B), conditions=[Implies(Not(B), Not(A)), inBool(B)])


doubleNegateConclusion = Forall((A, B), Implies(A, Not(Not(B))), conditions=[Implies(A, B), inBool(B)])

transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), domain=Booleans)

transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), conditions=inBool(B))

transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), domain=Booleans)

iffOverBoolImplEq = Forall((A, B), Equals(A, B), conditions=[Iff(A, B)], domain=Booleans)

implicationClosure = Forall((A, B), inBool(Implies(A, B)), domain=Booleans)

iffClosure = Forall((A, B), inBool(Iff(A, B)), domain=Booleans)

endTheorems(locals(), __package__)
