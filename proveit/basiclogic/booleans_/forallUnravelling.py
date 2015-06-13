from proveit.basiclogic import *

hypothesis = Forall((xStar, yStar), P_of_xStar_yStar, (multiQ_of_xStar, multiR_of_yStar))
conclusion = hypothesis.specialize().generalize(yStar, multiR_of_yStar).generalize(xStar, multiQ_of_xStar).prove({hypothesis})
booleans.qed('forallUnravelling', Implies(hypothesis, conclusion).generalize((P, multiQ, multiR)))
