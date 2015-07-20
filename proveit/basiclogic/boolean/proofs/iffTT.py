from proveit.basiclogic.boolean.axioms import iffDef
from proveit.basiclogic.boolean.theorems import impliesTT
from proveit.basiclogic import compose, TRUE, deriveStmtEqTrue
from proveit.basiclogic.variables import A, B

# TRUE => TRUE
TimplT = impliesTT.deriveViaBooleanEquality()
# (TRUE => TRUE) and (TRUE => TRUE) = TRUE
TimplTandTimplT_eq_T = deriveStmtEqTrue(compose(TimplT, TimplT))
# (TRUE <=> TRUE) = TRUE
iffDef.specialize({A:TRUE, B:TRUE}).applyTransitivity(TimplTandTimplT_eq_T).qed(__file__)