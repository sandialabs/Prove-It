from proveit.basiclogic.boolean.axioms import iffDef
from proveit.basiclogic.boolean.theorems import impliesFF
from proveit.basiclogic import compose, FALSE, deriveStmtEqTrue
from proveit.common import A, B

# FALSE => FALSE
FimplF = impliesFF.deriveViaBooleanEquality()
# (FALSE => FALSE) and (FALSE => FALSE) = TRUE
FimplFandFimplF_eq_T = deriveStmtEqTrue(compose(FimplF, FimplF))
# (FALSE <=> FALSE) = TRUE
iffDef.instantiate({A:FALSE, B:FALSE}).applyTransitivity(FimplFandFimplF_eq_T).qed(__file__)