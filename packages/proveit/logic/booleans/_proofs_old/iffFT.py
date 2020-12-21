from proveit.basiclogic.booleans.axioms import iff_def, and_t_f, implies_t_f
from proveit.basiclogic.booleans.theorems import implies_f_t
from proveit.basiclogic import TRUE, FALSE, Implies, And, Equation
from proveit.common import A, B, X

# (FALSE <=> TRUE) = [(FALSE => TRUE) and (TRUE => FALSE)]
eqn = Equation(iff_def.instantiate({A:FALSE, B:TRUE})).proven()
# (FALSE <=> TRUE) = [TRUE and (TRUE => FALSE)]
eqn.update(implies_f_t.substitution(eqn.eq_expr.rhs)).proven()
# (FALSE <=> TRUE) = (TRUE and FALSE)
eqn.update(implies_t_f.substitution(eqn.eq_expr.rhs)).proven()
# (FALSE <=> TRUE) = FALSE
eqn.update(and_t_f).qed(__file__)
