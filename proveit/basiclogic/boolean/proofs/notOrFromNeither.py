from proveit.basiclogic.boolean.axioms import orFF
from proveit.basiclogic.boolean.theorems import notFalse
from proveit.basiclogic import Implies, Not, Or, FALSE
from proveit.common import A, B, X

# Not(A or B) = Not(F or B) assuming Not(A)
notAorB_eq_notForB = Not(A).equateNegatedToFalse().substitution(X, Not(Or(X, B))).proven({Not(A)})
# Not(A or B) = Not(F or F) assuming Not(A), Not(B)
notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(Not(B).equateNegatedToFalse().substitution(X, Not(Or(FALSE, X)))).proven({Not(A), Not(B)})
#  Not(A or B) = Not(F) assuming Not(A), Not(B)
notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(orFF.substitution(X, Not(X))).proven({Not(A), Not(B)})
# Not(FALSE)
notFalse
# Not(A or B) assuming Not(A), Not(B)
notAorB = notAorB_eq_notF.deriveLeftViaEquivalence().proven({Not(A), Not(B)})
# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
Implies(Not(A), Implies(Not(B), notAorB)).generalize((A, B)).qed(__file__)
