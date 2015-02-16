from basiclogic import *

# Not(A or B) = Not(F or B) assuming Not(A)
notAorB_eq_notForB = Not(A).equateNegatedToFalse().substitution(X, Not(Or(X, B))).prove({Not(A)})
# Not(A or B) = Not(F or F) assuming Not(A), Not(B)
notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(Not(B).equateNegatedToFalse().substitution(X, Not(Or(FALSE, X)))).prove({Not(A), Not(B)})
#  Not(A or B) = Not(F) assuming Not(A), Not(B)
notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(booleans.orFF.substitution(X, Not(X))).prove({Not(A), Not(B)})
# Not(FALSE)
booleans.notFalse
# Not(A or B) assuming Not(A), Not(B)
notAorB = notAorB_eq_notF.deriveLeftViaEquivalence().prove({Not(A), Not(B)})
# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
booleans.qed('notOrFromNeither', Implies(Not(A), Implies(Not(B), notAorB)).generalize((A, B)))
