from basiclogic import *

hypothesis = Equals(TRUE, A)
booleans.qed('eqTrueRevElim', Implies(hypothesis, hypothesis.deriveReversed().deriveViaBooleanEquality()).generalize(A))
