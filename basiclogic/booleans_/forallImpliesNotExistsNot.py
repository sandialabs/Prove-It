from proveit.basiclogic import *

# hypothesis = forall_{x* | Q*(x*)} P(x*)
hypothesis = Forall(xStar, P_of_xStar, multiQ_of_xStar)
# [exists_{x* | Q*(x*)} Not(P(x*))] => [Not(forall_{x* | Q*(x*)} P(x*)]
existsNotImpliesNotForallSpec = booleans.existsNotImpliesNotForall.specialize().prove()
# exists_{x* | Q*(x*)} Not(P(x*)) in BOOLEANS
existsNotImpliesNotForallSpec.hypothesis.deduceInBool()
# forall_{x* | Q*(x*)} P(x*) in BOOLEANS
existsNotImpliesNotForallSpec.conclusion.operand.deduceInBool()
# NotExists_{x* | Q*(x*)} Not(P(x*))
conclusion = existsNotImpliesNotForallSpec.transpose().deriveConclusion().deriveNotExists().prove({hypothesis})
# forall_{P, Q*} NotExists_{x* | Q*(x*)} Not(P(x*)) => forall_{x* | Q*(x*)} P(x*)
booleans.qed('forallImpliesNotExistsNot', Implies(hypothesis, conclusion).generalize((P, multiQ)))
