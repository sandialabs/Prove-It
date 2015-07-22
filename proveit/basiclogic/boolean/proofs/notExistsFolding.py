from proveit.basiclogic.boolean.axioms import notExistsDef
from proveit.basiclogic.variables import P, S
from proveit.basiclogic.simpleExpr import etcQ

notExistsDef.specialize().leftImplViaEquivalence().generalize((P, etcQ, S)).qed(__file__)
