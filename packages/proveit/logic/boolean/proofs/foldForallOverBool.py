from proveit.basiclogic import BOOLEANS, TRUE, FALSE, inBool, Implies, And, deriveStmtEqTrue, Equals
from proveit.common import A, P, PofA
from proveit.basiclogic.common import PofTrue, PofFalse

# hypothesis = [P(TRUE) and P(FALSE)]
hypothesis = And(PofTrue, PofFalse)
# inBool(A=TRUE), inBool(A=FALSE), inBool(P(A) = TRUE)
AeqT = Equals(A, TRUE)
AeqF = Equals(A, FALSE)
PofAeqT = Equals(PofA, TRUE)
for eqExpr in (AeqT, AeqF, PofAeqT):
    eqExpr.deduceInBool()
# P(TRUE), P(FALSE) assuming hypothesis
for case in hypothesis.decompose(): case.proven({hypothesis})
# A=TRUE => P(A)=TRUE assuming hypothesis
Implies(AeqT, deriveStmtEqTrue(AeqT.subLeftSideInto(PofA, A))).proven({hypothesis})
# A=FALSE => P(A)=TRUE assuming hypothesis
Implies(AeqF, deriveStmtEqTrue(AeqF.subLeftSideInto(PofA, A))).proven({hypothesis})
# P(A) assuming hypothesis, (A in BOOLEANS)
inBool(A).unfold().deriveCommonConclusion(PofAeqT).deriveViaBooleanEquality().proven({hypothesis, inBool(A)})
# forall_{P} P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
Implies(hypothesis, PofA.generalize(A, domain=BOOLEANS)).generalize(P).qed(__file__)
