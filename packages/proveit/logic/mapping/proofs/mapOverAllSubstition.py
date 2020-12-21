from proveit.basiclogic import *

# hypothesis = forall_{x} [f(x) = g(x)]
hypothesis = Forall([x], fx_eq_gx)
# forall_{x | TRUE} [f(x) = g(x)] assuming hypothesis
hypothesis.instantiate().generalize([x], [TRUE]).prove({hypothesis})
# {[(y | TRUE) -> f(y)] = [(y | TRUE) -> g(y)] assuming hypothesis
fmap_given_T_eq_gmap_given_T = mapping.map_substitution.instantiate(
    {Qx: TRUE}).derive_conclusion().prove({hypothesis})
# [y -> f(y)] = [(y | TRUE) -> g(y)] assuming hypothesis
fmap_eq_gmap_given_T = mapping.lambda_over_all_def.instantiate(
    {x: y}).apply_transitivity(fmap_given_T_eq_gmap_given_T).prove({hypothesis})
# [y -> f(y)] = [y -> g(y)] assuming hypothesis
fmap_eq_gmap = mapping.lambda_over_all_def.instantiate({f: g, x: y}).apply_transitivity(
    fmap_eq_gmap_given_T).derive_reversed().prove({hypothesis})
# {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
mapping.qed('map_over_all_substition', Implies(
    hypothesis, fmap_eq_gmap).generalize([f, g]))
