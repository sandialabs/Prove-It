from proveit.expression import Operation, Lambda
from proveit.statement import Axioms
from proveit.basiclogic import Forall, Equals, In, TRUE, Iff, Implies, And
from .mapping_ops import Domain, CoDomain
from proveit.common import f, g, x, y, Q, fx, fy, gx, Qx, Qy

fx_map = Lambda(x, fx) # x -> f(x)
fx_given_qx_map = Lambda(x, fx, Qx) # x -> f(x) | Q(x)
gx_given_qx_map = Lambda(x, gx, Qx) # x -> g(x) | Q(x)
f_domain_eq_gDomain = Equals(Domain(f), Domain(g)) # Domain(f) = Domain(g)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
x_in_f_domain = In(x, Domain(f)) # x in Domain(f)
f_eq_g = Equals(f, g) # f = g

mapping_axioms = Axioms(__package__, locals())

map_application = Forall((f, Q), Forall(y, Equals(Operation(fx_given_qx_map, y), fy), Qy))

# forall_{f} [x -> f(x)] = [x -> f(x) | TRUE]
lambda_over_all_def = Forall(f, Equals(Lambda(x, fx), Lambda(x, fx, TRUE)))

# forall_{f, Q} forall_{y} y in Domain(x -> f(x) | Q(x)) <=> Q(y)
lambda_domain_def = Forall((f, Q), Forall(y, Iff(In(y, Domain(fx_given_qx_map)), Qy)))

# forall_{f, g} [Domain(f) = Domain(g) and forall_{x in Domain(f)} f(x) = g(x)] => (f = g)}
map_is_as_map_does = Forall((f, g), Implies(And(f_domain_eq_gDomain, Forall(x, fx_eq_gx, x_in_f_domain)), f_eq_g))

mapping_axioms.finish(locals())