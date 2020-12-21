from proveit.basiclogic import *

# y in Domain((x | Q(x)) -> f(x)) <=> Q(y)
y_in_fmap_iff_Qy = mapping.lambda_domain_def.instantiate().instantiate().prove()
# y in Domain((x | Q(x)) -> g(x)) <=> Q(y)
y_in_gmap_iff_Qy = mapping.lambda_domain_def.instantiate(
    {f: g}).instantiate().prove()
# forall_{x} x in Domain((x | Q(x)) -> f(x)) <=> x in Domain((x | Q(x)) ->
# g(x))
y_in_fmap_iff_y_in_gmap = y_in_fmap_iff_Qy.apply_transitivity(
    y_in_gmap_iff_Qy).generalize(y).prove()
# forall_{f, g, Q} Domain((x | Q(x)) -> f(x)) = Domain((x | Q(x)) -> g(x))
mapping.qed('lambda_domain_equality', sets.set_is_as_set_contains.instantiate({x: y, A: Domain(
    fx_given_qx_map), B: Domain(gx_given_qx_map)}).derive_conclusion().generalize((f, g, Q)))
