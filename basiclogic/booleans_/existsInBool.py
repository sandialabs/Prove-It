from proveit.basiclogic import *

# exists_{x* | Q*(x*)} P(x*) = not(forall_{x* | Q*(x*)} P(x*) != TRUE)
existsDefSpec = booleans.existsDef.specialize().prove()
# [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = TRUE] or [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = FALSE]
rhsTrue, rhsFalse = existsDefSpec.rhs.deduceInBool().unfold().prove().operands
# exists_{x* | Q*(x*)} P(x*) in BOOLEANS assuming [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = TRUE]
existsInBoolSpec = rhsTrue.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsTrue})
# exists_{x* | Q*(x*)} P(x*) in BOOLEANS assuming [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = FALSE]
rhsFalse.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsFalse})
# deduce rhsTrue, rhsFals, existsInBoolSpec all in BOOLEANS
for expr in (rhsTrue, rhsFalse, existsInBoolSpec): expr.deduceInBool()
# forall_{P, Q*} exists_{x* | Q*(x*)} P(x*) in BOOLEANS
booleans.qed('existsInBool', Or(rhsTrue, rhsFalse).deriveCommonConclusion(existsInBoolSpec).generalize((P, multiQ)))
