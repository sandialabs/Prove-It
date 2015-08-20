from proveit.basiclogic import And, Implies, Iff
from proveit.common import A, B, C

# hypothesis = (A <=> B) and (B <=> C)
hypothesis = And(Iff(A, B), Iff(B, C))
AiffB, BiffC = hypothesis.decompose()
# B assuming A <=> B and A
AiffB.deriveRight().proven({AiffB, A})
# A => C assuming A <=> B, B <=> C
Implies(A, BiffC.deriveRight()).proven({hypothesis})
# C assuming B <=> C and C
BiffC.deriveLeft().proven({BiffC, C})
# C => A assuming A <=> B, B <=> C
Implies(C, AiffB.deriveLeft()).proven({hypothesis})
# A <=> C assuming hypothesis
AiffC = Iff(A, C).concludeViaComposition().proven({hypothesis})
# forall_{A, B, C} (A <=> B and B <=> C) => (A <=> C)
Implies(hypothesis, AiffC).generalize((A, B, C)).qed(__file__)
