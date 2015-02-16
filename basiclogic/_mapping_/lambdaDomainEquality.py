from basiclogic import *

# y in Domain((x | Q(x)) -> f(x)) <=> Q(y)
y_in_fmap_iff_Qy = mapping.lambdaDomainDef.specialize().specialize().prove()
# y in Domain((x | Q(x)) -> g(x)) <=> Q(y)
y_in_gmap_iff_Qy = mapping.lambdaDomainDef.specialize({f:g}).specialize().prove()
# forall_{x} x in Domain((x | Q(x)) -> f(x)) <=> x in Domain((x | Q(x)) -> g(x))
y_in_fmap_iff_y_in_gmap = y_in_fmap_iff_Qy.applyTransitivity(y_in_gmap_iff_Qy).generalize(y).prove()
# forall_{f, g, Q} Domain((x | Q(x)) -> f(x)) = Domain((x | Q(x)) -> g(x))
mapping.qed('lambdaDomainEquality', sets.setIsAsSetContains.specialize({x:y, A:Domain(fxGivenQxMap), B:Domain(gxGivenQxMap)}).deriveConclusion().generalize((f, g, Q)))
