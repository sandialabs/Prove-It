from basiclogic import *

# hypothesis = (FALSE=A)
hypothesis = Equals(FALSE, A)
# inBool(FALSE)
booleans.falseInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} (FALSE=A) => inBool(A)
booleans.qed('inBoolIfEqFalseRev', Implies(hypothesis, conclusion).generalize(A))
