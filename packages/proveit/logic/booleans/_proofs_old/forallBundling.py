from proveit.basiclogic import Forall, Implies
from proveit.common import P, S, x_etc, y_etc, Qetc, Retc, Pxy_etc, etc_Qx_etc, etc_Ry_etc

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
hypothesis = Forall(x_etc, Forall(y_etc, Pxy_etc, S, etc_Ry_etc), S, etc_Qx_etc)
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
conclusion = hypothesis.instantiate().instantiate().generalize((x_etc, y_etc), S, (etc_Qx_etc, etc_Ry_etc)).proven({hypothesis})
# forall_{P, ..Q.., ..R.., S} [forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)]
Implies(hypothesis, conclusion).generalize((P, Qetc, Retc, S)).qed(__file__)
