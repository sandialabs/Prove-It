from proveit.basiclogic import *

# [exists_{x* | Q*(x*)} P(x*)] = not(forall_{x* | Q*(x*)} (P(x*) != TRUE))
existsDefSpec = booleans.existsDef.specialize().prove()
# notexists_{x* | Q*(x*)} P(x*) = not[exists_{x* | Q*(x*)} P(x*)]
notExistsDefSpec = booleans.notExistsDef.specialize().prove()
# rhs = forall_{x* | Q*(x*)} (P(x*) != TRUE)
rhs = Forall(xStar, NotEquals(P_of_xStar, TRUE), multiQ_of_xStar)
# [forall_{x* | Q*(x*)} (P(x*) != TRUE)] in BOOLEANS
rhs.deduceInBool().prove()
# not(not(forall_{x* | Q*(x*)} (P(x*) != TRUE))) = forall_{x* | Q*(x*)} (P(x*) != TRUE))
doubleNegatedForall = Not(Not(rhs)).deduceDoubleNegationEquiv().deriveReversed().prove()
# notexists_{x* | Q*(x*)} P(x*) = forall_{x* | Q*(x*)} (P(x*) != TRUE))
equiv = notExistsDefSpec.applyTransitivity(existsDefSpec.substitution(X, Not(X))).applyTransitivity(doubleNegatedForall).prove()
# forall_{P, Q*} [notexists_{x* | Q*(x*)} P(x*) = forall_{x* | Q*(x*)} (P(x*) != TRUE)]
booleans.qed('existsDefNegation', equiv.generalize((P, multiQ)))
