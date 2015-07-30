from proveit.basiclogic.boolean.axioms import iffDef, andTF, impliesTF
from proveit.basiclogic.boolean.theorems import impliesFT
from proveit.basiclogic import TRUE, FALSE, Implies, And, Equation
from proveit.common import A, B, X

# (FALSE <=> TRUE) = [(FALSE => TRUE) and (TRUE => FALSE)]
eqn = Equation(iffDef.specialize({A:FALSE, B:TRUE})).prove()
# (FALSE <=> TRUE) = [TRUE and (TRUE => FALSE)]
eqn.update(impliesFT.substitution(X, And(X, Implies(TRUE, FALSE)))).prove()
# (FALSE <=> TRUE) = (TRUE and FALSE)
eqn.update(impliesTF.substitution(X, And(TRUE, X)).prove())
# (FALSE <=> TRUE) = FALSE
eqn.update(andTF).qed(__file__)
