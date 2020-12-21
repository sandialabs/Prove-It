from proveit.basiclogic.booleans.theorems import double_negation, from_double_negation
from proveit.basiclogic import BOOLEANS, in_bool, Not, Iff
from proveit.common import A

# A => Not(Not(A))
double_negation_implied = double_negation.instantiate().proven()
# Not(Not(A)) => A
implies_double_negation = from_double_negation.instantiate().proven()
# [A => Not(Not(A))] in BOOLEANS if A in BOOLEANS
double_negation_implied.deduce_in_bool().proven({in_bool(A)})
# [Not(Not(A)) => A] in BOOLEANS if A in BOOLEANS
implies_double_negation.deduce_in_bool().proven({in_bool(A)})
# forall_{A} A = Not(Not(A))
Iff(A, Not(Not(A))).conclude_via_composition().derive_equality(
).generalize(A, domain=BOOLEANS).qed(__file__)
