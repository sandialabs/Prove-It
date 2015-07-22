from proveit.basiclogic import Forall, Implies
from proveit.common import P, S, xEtc, yEtc, Qetc, Retc, PxyEtc, etc_QxEtc, etc_RyEtc

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
hypothesis = Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
conclusion = hypothesis.specialize().specialize().generalize((xEtc, yEtc), S, (etc_QxEtc, etc_RyEtc)).prove({hypothesis})
# forall_{P, ..Q.., ..R.., S} [forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)]
Implies(hypothesis, conclusion).generalize((P, Qetc, Retc, S)).qed(__file__)
