from proveit.basiclogic import Implies, Equals, TRUE
from proveit.common import A

hypothesis = Equals(TRUE, A)
Implies(hypothesis, hypothesis.deriveReversed().deriveViaBooleanEquality()).generalize(A).qed(__file__)
