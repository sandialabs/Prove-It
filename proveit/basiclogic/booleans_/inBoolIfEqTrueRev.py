from proveit.basiclogic import *

# hypothesis = (TRUE=A)
hypothesis = Equals(TRUE, A)
# inBool(TRUE)
booleans.trueInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} (TRUE=A) => inBool(A)
booleans.qed('inBoolIfEqTrueRev', Implies(hypothesis, conclusion).generalize(A))
