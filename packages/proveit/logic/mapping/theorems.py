from proveit.statement import Theorems
from proveit.expression import Lambda, Operation
from proveit.basiclogic import Forall, Equals, Implies, In
from .mapping_ops import Domain
from proveit.common import f, g, x, y, Q, fx, fy, gx, gy, Qx, Qy
from proveit.basiclogic.common import fx_eq_gx

mapping_theorems = Theorems(__package__, locals())

lambda_domain_equality = Forall((f, g, Q), Equals(Domain(Lambda(x, fx, Qx)), Domain(Lambda(x, gx, Qx))))

# forall_{f, g, Q} {forall_{x | Q(x)} [f(x) = g(x)]} => {[(y | Q(y)) -> f(y)] = [(y | Q(y)) -> g(y)]
map_substitution = Forall((f, g, Q), Implies(Forall(x, fx_eq_gx, Qx), Equals(Lambda(y, fy, Qy), Lambda(y, gy, Qy))))

# forall_{f, g} {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
map_over_all_substitution = Forall((f, g), Implies(Forall(x, fx_eq_gx), Equals(Lambda(y, fy), Lambda(y, gy))))

mapping_theorems.finish(locals())
