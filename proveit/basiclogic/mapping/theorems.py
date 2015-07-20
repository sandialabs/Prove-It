from proveit.statement import Theorems
from proveit.expression import Lambda, Operation
from proveit.basiclogic import Forall, Equals, Implies, In
from mappingOps import Domain
from proveit.basiclogic.variables import f, g, x, y, Q

fx = Operation(f, x) # f(x)
fy = Operation(f, y) # f(y)
gx = Operation(g, x) # g(x)
gy = Operation(g, y) # g(y)
Qx = Operation(Q, x) # Q(x)
Qy = Operation(Q, y) # Q(y)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)

mappingTheorems = Theorems(__package__)

lambdaDomainEquality = Forall((f, g, Q), Equals(Domain(Lambda(x, fx, Qx)), Domain(Lambda(x, gx, Qx))))

# forall_{f, g, Q} {forall_{x | Q(x)} [f(x) = g(x)]} => {[(y | Q(y)) -> f(y)] = [(y | Q(y)) -> g(y)]
mapSubstitution = Forall((f, g, Q), Implies(Forall(x, fx_eq_gx, Qx), Equals(Lambda(y, fy, Qy), Lambda(y, gy, Qy))))

# forall_{f, g} {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
mapOverAllSubstitution = Forall((f, g), Implies(Forall(x, fx_eq_gx), Equals(Lambda(y, fy), Lambda(y, gy))))

mappingTheorems.finish(locals())
