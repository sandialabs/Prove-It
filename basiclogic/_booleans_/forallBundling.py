from basiclogic import *

hypothesis = Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar)
conclusion = hypothesis.specialize().specialize().generalize((xStar, yStar), (multiQ_of_xStar, multiR_of_yStar)).prove({hypothesis})
booleans.qed('forallBundling', Implies(hypothesis, conclusion).generalize((P, multiQ, multiR)))
