from proveit.basiclogic.booleans.axioms import iff_def, and_f_t, implies_t_f
from proveit.basiclogic.booleans.theorems import implies_f_t
from proveit.basiclogic import TRUE, FALSE, Implies, And, Equation
from proveit.common import A, B, X

# (TRUE <=> FALSE) = [(TRUE => FALSE) and (FALSE => TRUE)]
eqn = Equation(iff_def.instantiate({A: TRUE, B: FALSE})).proven()
# (TRUE <=> FALSE) = [FALSE and (FALSE => TRUE)]
eqn.update(implies_t_f.substitution(eqn.eq_expr.rhs)).proven()
# (TRUE <=> FALSE) = (FALSE and TRUE)
eqn.update(implies_f_t.substitution(eqn.eq_expr.rhs)).proven()
# (TRUE <=> FALSE) = FALSE
eqn.update(and_f_t).qed(__file__)
