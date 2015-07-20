from proveit.basiclogic import Implies, Not, FALSE
from proveit.basiclogic.variables import A

# FALSE assuming Not(A) and A
Not(A).equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), A})
Implies(Not(A), Implies(A, FALSE)).generalize(A).qed(__file__)
