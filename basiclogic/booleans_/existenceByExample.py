from basiclogic import *

# neverPy = [forall_{y* | Q*(y*)} (P(y*) != TRUE)]
neverPy = Forall(yStar, NotEquals(P_of_yStar, TRUE), multiQ_of_yStar)
# (P(x*) != TRUE) assuming Q*(x*), neverPy
neverPy.specialize({yStar:xStar}).prove({multiQ_of_xStar, neverPy})
# (TRUE != TRUE) assuming Q*(x*), P(x*), neverPy
trueNotEqTrue = deriveStmtEqTrue(P_of_xStar).rhsSubstitute(X, NotEquals(X, TRUE)).prove({multiQ_of_xStar, P_of_xStar, neverPy})
# FALSE assuming Q*(x*), P(x*), neverPy
trueNotEqTrue.evaluate().deriveContradiction().deriveConclusion().prove({multiQ_of_xStar, P_of_xStar, neverPy})
# [forall_{y* | Q*(y*)} (P(y*) != TRUE)] in BOOLEANS
neverPy.deduceInBool().prove()
# Not(forall_{y* | Q*(y*)} (P(y*) != TRUE) assuming Q*(x*), P(x*)
Implies(neverPy, FALSE).deriveViaContradiction().prove({multiQ_of_xStar, P_of_xStar})
# exists_{y* | Q*(y*)} P(y*) assuming Q*(x*), P(x*)
existence = booleans.existsDef.specialize({xStar:yStar}).deriveLeftViaEquivalence().prove({multiQ_of_xStar, P_of_xStar})
# forall_{P, Q*} forall_{x* | Q*(x*)} [P(*x) => exists_{y* | Q*(y*)} P(y*)]
booleans.qed('existenceByExample', Implies(P_of_xStar, existence).generalize(xStar, multiQ_of_xStar).generalize((P, multiQ)))
