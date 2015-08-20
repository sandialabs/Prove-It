from proveit.basiclogic.boolean.axioms import iffDef, andTF, impliesTF
from proveit.basiclogic.boolean.theorems import impliesFT
from proveit.basiclogic import TRUE, FALSE, Implies, And, Equation
from proveit.common import A, B, X

# (FALSE <=> TRUE) = [(FALSE => TRUE) and (TRUE => FALSE)]
eqn = Equation(iffDef.specialize({A:FALSE, B:TRUE})).proven()
# (FALSE <=> TRUE) = [TRUE and (TRUE => FALSE)]
eqn.update(impliesFT.substitution(X, And(X, Implies(TRUE, FALSE)))).proven()
# (FALSE <=> TRUE) = (TRUE and FALSE)
eqn.update(impliesTF.substitution(X, And(TRUE, X)).proven())
# (FALSE <=> TRUE) = FALSE
eqn.update(andTF).qed(__file__)
