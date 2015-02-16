from basiclogic import *

# hypothesis = (A=FALSE)
hypothesis = Equals(A, FALSE)
# inBool(FALSE)
booleans.falseInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} A=FALSE => inBool(A)
booleans.qed('inBoolIfEqFalse', Implies(hypothesis, conclusion).generalize(A))
