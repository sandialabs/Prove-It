from proveit.basiclogic import Implies, Iff
from proveit.common import A, B

hypothesis = Iff(A, B)  # hypothesis = (A <=> B)
# A => B given hypothesis
hypothesis.derive_right_implication().proven({hypothesis})
# B => A given hypothesis
hypothesis.derive_left_implication().proven({hypothesis})
# forall_{A, B} (A <=> B) => (B <=> A)
Implies(
    hypothesis, Iff(
        B, A).conclude_via_composition()).generalize(
            (A, B)).qed(__file__)
