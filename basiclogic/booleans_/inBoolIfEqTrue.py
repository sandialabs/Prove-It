from basiclogic import *

# hypothesis = (A=TRUE)
hypothesis = Equals(A, TRUE)
# inBool(TRUE)
booleans.trueInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} A=TRUE => inBool(A)
booleans.qed('inBoolIfEqTrue', Implies(hypothesis, conclusion).generalize(A))
