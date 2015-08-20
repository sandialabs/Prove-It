from proveit.basiclogic.boolean.theorems import existsNotImpliesNotForall
from proveit.basiclogic import Forall, Implies
from proveit.common import P, S, xEtc, PxEtc, Qetc, etc_QxEtc

# hypothesis = forall_{..x.. in S | ..Q(..x..)..} P(..x..)
hypothesis = Forall(xEtc, PxEtc, S, etc_QxEtc)
# [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))] => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
existsNotImpliesNotForallSpec = existsNotImpliesNotForall.specialize().proven()
# exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) in BOOLEANS
existsNotImpliesNotForallSpec.hypothesis.deduceInBool()
# forall_{..x.. in S | ..Q(..x..)..} P(..x..) in BOOLEANS
existsNotImpliesNotForallSpec.conclusion.operand.deduceInBool()
# NotExists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))
conclusion = existsNotImpliesNotForallSpec.transpose().deriveConclusion().deriveNotExists().proven({hypothesis})
# forall_{P, ..Q.., S} NotExists_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) => forall_{..x.. in S | ..Q(..x..)..} P(..x..)
Implies(hypothesis, conclusion).generalize((P, Qetc, S)).qed(__file__)
