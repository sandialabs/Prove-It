from proveit.basiclogic import *

fy_given_qy_map = Lambda([y], fy, [Qy]) # (x | Q(x)) -> f(x)
gy_given_qy_map = Lambda([y], gy, [Qy]) # (x | Q(x)) -> g(x)
# hypothesis = forall_{x | Q(x)} [f(x) = g(x)]
hypothesis = Forall([x], fx_eq_gx, [Qx])
# [(y | Q(y)) -> f(y)](x) = f(x), assuming Q(x)
fmap_x_eq_fx = mapping.map_application.instantiate().instantiate({x:y, y:x}).prove({Qx})
# [(y | Q(y)) -> g(y)](x) = g(x), assuming Q(x)
gmap_x_eq_gx = mapping.map_application.instantiate({f:g}).instantiate({x:y, y:x}).prove({Qx})
# [(y | Q(y)) -> f(y)](x) = g(x), assuming hypothesis, Q(x)
fmap_x_eq_gx = fmap_x_eq_fx.apply_transitivity(hypothesis.instantiate()).prove({hypothesis, Qx})
# [(y | Q(y)) -> f(y)](x) = [(y | Q(y)) -> g(y)](x), assuming hypothesis, Q(x)
fmap_x_eq_g_map_x = fmap_x_eq_gx.apply_transitivity(gmap_x_eq_gx).prove({hypothesis, Qx})
# [x in Domain((y | Q(y)) -> f(y))] => Q(x)
mapping.lambda_domain_def.instantiate().instantiate({x:y, y:x}).derive_right_implication().prove(Qx)
# forall_{x in Domain([(y | Q(y)) -> f(y)])} [(y | Q(y)) -> f(y)](x) = [(y | Q(y)) -> g(y)](x), assumping hypothesis
same_map_under_domain = fmap_x_eq_g_map_x.generalize(x, In(x, Domain(Lambda(y, fy, Qy)))).prove({hypothesis})
# Domain((y | Q(y)) -> f(y)) = Domain((y | Q(y)) -> g(y))
domain_equality = mapping.lambda_domain_equality.instantiate({x:y}).prove()
# Domain((y | Q(y)) -> f(y)) = Domain((y | Q(y)) -> g(y)) and forall_{x in Domain([(y | Q(y)) -> f(y)])} [(y | Q(y)) -> f(y)](x) = [(y | Q(y)) -> g(y)](x), assumping hypothesis
compose(domain_equality, same_map_under_domain).prove({hypothesis})
# {forall_{x | Q(x)} [f(x) = g(x)]} => {[(y | Q(y)) -> f(y)] = [(y | Q(y)) -> g(y)]
mapping.qed('map_substitution', Implies(hypothesis, mapping.map_is_as_map_does.instantiate({f:fy_given_qy_map, g:gy_given_qy_map}).derive_conclusion()).generalize([f, g, Q]))
