from basiclogic import *

# forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*) => forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
forallBundlingSpec = booleans.forallBundling.specialize().prove()
# forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*) => forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x, y*)
booleans.forallUnravelling.specialize().prove()
# lhs = forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*)
# rhs = forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
lhs, rhs = forallBundlingSpec.conclusion, forallBundlingSpec.hypothesis
# lhs in BOOLEANS, rhs in BOOLEANS
for expr in (lhs, rhs): expr.deduceInBool().prove()
# lhs = rhs
equiv = Iff(lhs, rhs).concludeViaComposition().deriveEquality().prove()
booleans.qed('forallBundledEquiv', equiv.generalize((P, multiQ, multiR)))
