from proveit.basiclogic.booleans.theorems import exists_not_implies_not_forall
from proveit.basiclogic import Forall, Implies
from proveit.common import P, S, x_etc, Px_etc, Qetc, etc_Qx_etc

# hypothesis = forall_{..x.. in S | ..Q(..x..)..} P(..x..)
hypothesis = Forall(x_etc, Px_etc, S, etc_Qx_etc)
# [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))] => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
exists_not_implies_not_forall_spec = exists_not_implies_not_forall.instantiate().proven()
# exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) in BOOLEANS
exists_not_implies_not_forall_spec.hypothesis.deduce_in_bool()
# forall_{..x.. in S | ..Q(..x..)..} P(..x..) in BOOLEANS
exists_not_implies_not_forall_spec.conclusion.operand.deduce_in_bool()
# NotExists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))
conclusion = exists_not_implies_not_forall_spec.transpose().derive_conclusion().derive_not_exists().proven({hypothesis})
# forall_{P, ..Q.., S} NotExists_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) => forall_{..x.. in S | ..Q(..x..)..} P(..x..)
Implies(hypothesis, conclusion).generalize((P, Qetc, S)).qed(__file__)
