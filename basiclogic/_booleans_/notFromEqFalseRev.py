from basiclogic import *

# FeqA := (F=A)
FeqA = Equals(FALSE, A)
# Not(A) assuming FeqA
notA = FeqA.deriveReversed().deriveViaBooleanEquality().prove({FeqA})
booleans.qed('notFromEqFalseRev', Implies(FeqA, notA).generalize(A))
