from proveit.basiclogic.boolean.axioms import notExistsDef
from proveit.common import P, S, Qetc

notExistsDef.instantiate().rightImplViaEquivalence().generalize((P, Qetc, S)).qed(__file__)
