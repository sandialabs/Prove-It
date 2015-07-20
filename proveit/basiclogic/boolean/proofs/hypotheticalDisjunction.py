from proveit.basiclogic.boolean.axioms import notT
from proveit.basiclogic import BOOLEANS, FALSE, inBool, Implies, And, Or, Not, deriveStmtEqTrue
from proveit.basiclogic.variables import A, B, C, X

AorB = Or(A, B)
hypothesis = And(Implies(A, C), Implies(B, C))
ABCareBool = {inBool(A), inBool(B), inBool(C)}
# A=>C, B=>C assuming (A=>C and B=>C)
AimplC, _ = hypothesis.decompose()
# Not(A) assuming inBool(A), inBool(B), (A=>C and B=>C), Not(C)
AimplC.transpose().deriveConclusion().prove({inBool(A), inBool(C), hypothesis, Not(C)})
# B assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
AorB.deriveRightIfNotLeft().prove(ABCareBool | {hypothesis, AorB, Not(C)})
# Not(TRUE) assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
deriveStmtEqTrue(C).rhsSubstitute(X, Not(X)).prove(ABCareBool | {hypothesis, AorB, Not(C)})
# FALSE assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
notT.deriveRightViaEquivalence().prove(ABCareBool | {hypothesis, AorB, Not(C)})
# Contradiction proof of C assuming (A=>C and B=>C), (A or B), inBool(A), and inBool(B)
Implies(Not(C), FALSE).deriveViaContradiction().prove(ABCareBool | {hypothesis, AorB})
# forall_{A, B, C in BOOLEANS} (A=>C and B=>C) => ((A or B) => C)
Implies(hypothesis, Implies(AorB, C)).generalize((A, B, C), domain=BOOLEANS).qed(__file__)
