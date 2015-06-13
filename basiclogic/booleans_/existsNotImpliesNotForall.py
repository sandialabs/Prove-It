from proveit.basiclogic import *

# existsNot = [exists_{x* | Q*(x*)} Not(P(x*))]
existsNot = Exists(xStar, Not(P_of_xStar), multiQ_of_xStar)
# [Not(forall_{x* | Q(x*)} Not(P(x*)) != TRUE] assuming existsNot
booleans.existsDef.specialize({Operation(P, xStar):Not(P_of_xStar)}).deriveRightViaEquivalence().prove({existsNot})
# forall_{x* | Q(x*)} P(x*)
forallPx = Forall(xStar, P_of_xStar, multiQ_of_xStar)
# forall_{x* | Q(x*)} Not(P(x*)) != TRUE
forallNotPxNotTrue = Forall(xStar, NotEquals(Not(P_of_xStar), TRUE), multiQ_of_xStar)
# forallPx in BOOLEANS, forallNotPxNotTrue in BOOLEANS
for expr in (forallPx, forallNotPxNotTrue):
    expr.deduceInBool().prove()
# Not(TRUE) != TRUE
NotEquals(Not(TRUE), TRUE).proveByEval()
# forallNotPxNotTrue assuming forallPx, Q*(x*)
deriveStmtEqTrue(forallPx.specialize()).lhsStatementSubstitution(X, NotEquals(Not(X), TRUE)).deriveConclusion().generalize(xStar, multiQ_of_xStar).prove({forallPx})
# Not(forallNotPxNotTrue) => Not(forallPx)
Implies(forallPx, forallNotPxNotTrue).transpose().prove()
# forall_{P, Q*} [exists_{x* | Q*(x*)} Not(P(x*))] => [Not(forall_{x* | Q*(x*)} P(x*)]
booleans.qed('existsNotImpliesNotForall', Implies(existsNot, Not(forallPx)).generalize((P, multiQ)))
