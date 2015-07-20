from proveit.basiclogic import Forall, Implies
from proveit.basiclogic.variables import P, S
from proveit.basiclogic.simpleExpr import xEtc, yEtc, etcQ, etcR, PxyEtc, etc_QxEtc, etc_RyEtc

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
hypothesis = Forall(xEtc, Forall(yEtc, PxyEtc, etc_RyEtc, domain=S), etc_QxEtc, domain=S)
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
conclusion = hypothesis.specialize().specialize().generalize((xEtc, yEtc), (etc_QxEtc, etc_RyEtc), domain=S).prove({hypothesis})
# forall_{P, ..Q.., ..R.., S} [forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)]
Implies(hypothesis, conclusion).generalize((P, etcQ, etcR)).qed(__file__)
