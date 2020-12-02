from proveit.basiclogic import *

# hypothesis = forall_{x} [f(x) = g(x)]
hypothesis = Forall([x], fx_eq_gx)
# forall_{x | TRUE} [f(x) = g(x)] assuming hypothesis
hypothesis.instantiate().generalize([x], [TRUE]).prove({hypothesis})
# {[(y | TRUE) -> f(y)] = [(y | TRUE) -> g(y)] assuming hypothesis
fmap_given_T_eq_gmap_given_T = mapping.mapSubstitution.instantiate({Qx:TRUE}).deriveConclusion().prove({hypothesis})
# [y -> f(y)] = [(y | TRUE) -> g(y)] assuming hypothesis
fmap_eq_gmap_given_T = mapping.lambdaOverAllDef.instantiate({x:y}).applyTransitivity(fmap_given_T_eq_gmap_given_T).prove({hypothesis})
# [y -> f(y)] = [y -> g(y)] assuming hypothesis
fmap_eq_gmap = mapping.lambdaOverAllDef.instantiate({f:g, x:y}).applyTransitivity(fmap_eq_gmap_given_T).deriveReversed().prove({hypothesis})
# {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
mapping.qed('mapOverAllSubstition', Implies(hypothesis, fmap_eq_gmap).generalize([f, g]))
