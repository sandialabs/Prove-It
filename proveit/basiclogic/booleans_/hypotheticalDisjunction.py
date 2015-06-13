from proveit.basiclogic import *

AorB = Or(A, B)
hypothesis = And(Implies(A, C), Implies(B, C))
ABCareBoolInOrder = [inBool(A), inBool(B), inBool(C)]
ABCareBool = set(ABCareBoolInOrder)
# A=>C, B=>C assuming (A=>C and B=>C)
AimplC, _ = hypothesis.decompose()
# Not(A) assuming inBool(A), inBool(B), (A=>C and B=>C), Not(C)
AimplC.transpose().deriveConclusion().prove({inBool(A), inBool(C), hypothesis, Not(C)})
# B assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
AorB.deriveRightIfNotLeft().prove(ABCareBool | {hypothesis, AorB, Not(C)})
# Not(TRUE) assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
deriveStmtEqTrue(C).rhsSubstitute(X, Not(X)).prove(ABCareBool | {hypothesis, AorB, Not(C)})
# FALSE assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
booleans.notT.deriveRightViaEquivalence().prove(ABCareBool | {hypothesis, AorB, Not(C)})
# Contradiction proof of C assuming (A=>C and B=>C), (A or B), inBool(A), and inBool(B)
Implies(Not(C), FALSE).deriveViaContradiction().prove(ABCareBool | {hypothesis, AorB})
booleans.qed('hypotheticalDisjunction', Implies(hypothesis, Implies(AorB, C)).generalize((A, B, C), ABCareBoolInOrder))
