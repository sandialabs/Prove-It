from proveit.basiclogic.boolean.axioms import notExistsDef
from proveit.common import P, S, Qetc

notExistsDef.specialize().leftImplViaEquivalence().generalize((P, Qetc, S)).qed(__file__)
