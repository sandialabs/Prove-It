from basiclogic import *

hypothesis = Iff(A, B) # hypothesis = (A <=> B)
# A => B given hypothesis
hypothesis.deriveRightImplication().prove({hypothesis})
# B => A given hypothesis
hypothesis.deriveLeftImplication().prove({hypothesis})
# forall_{A, B} (A <=> B) => (B <=> A)
booleans.qed('iffSymmetry', Implies(hypothesis, Iff(B, A).concludeViaComposition()).generalize((A, B)))
