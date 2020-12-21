from proveit.basiclogic import Implies, Equals, TRUE
from proveit.common import A

hypothesis = Equals(TRUE, A)
Implies(hypothesis, hypothesis.derive_reversed(
).derive_via_boolean_equality()).generalize(A).qed(__file__)
