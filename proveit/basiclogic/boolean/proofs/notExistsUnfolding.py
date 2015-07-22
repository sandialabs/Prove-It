from proveit.basiclogic.boolean.axioms import notExistsDef
from proveit.basiclogic.variables import P
from proveit.basiclogic.simpleExpr import etcQ

notExistsDef.specialize().rightImplViaEquivalence().generalize((P, etcQ)).qed(__file__)
