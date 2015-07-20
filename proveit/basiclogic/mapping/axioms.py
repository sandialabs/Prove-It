from proveit.expression import Operation, Lambda
from proveit.statement import Axioms
from proveit.basiclogic import Forall, Equals, In, TRUE, Iff, Implies, And
from mappingOps import Domain, CoDomain
from proveit.basiclogic.variables import f, g, x, y, Q

fx = Operation(f, x) # f(x)
fy = Operation(f, y) # f(y)
gx = Operation(g, x) # g(x)
Qx = Operation(Q, x) # Q(x)
Qy = Operation(Q, y) # Q(y)
fxMap = Lambda(x, fx) # x -> f(x)
fxGivenQxMap = Lambda(x, fx, Qx) # x -> f(x) | Q(x)
gxGivenQxMap = Lambda(x, gx, Qx) # x -> g(x) | Q(x)
fDomain_eq_gDomain = Equals(Domain(f), Domain(g)) # Domain(f) = Domain(g)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
x_in_fDomain = In(x, Domain(f)) # x in Domain(f)
f_eq_g = Equals(f, g) # f = g

mappingAxioms = Axioms(__package__)

mapApplication = Forall((f, Q), Forall(y, Equals(Operation(fxGivenQxMap, y), fy), Qy))

# forall_{f} [x -> f(x)] = [x -> f(x) | TRUE]
lambdaOverAllDef = Forall(f, Equals(Lambda(x, fx), Lambda(x, fx, TRUE)))

# forall_{f, Q} forall_{y} y in Domain(x -> f(x) | Q(x)) <=> Q(y)
lambdaDomainDef = Forall((f, Q), Forall(y, Iff(In(y, Domain(fxGivenQxMap)), Qy)))

# forall_{f, g} [Domain(f) = Domain(g) and forall_{x in Domain(f)} f(x) = g(x)] => (f = g)}
mapIsAsMapDoes = Forall((f, g), Implies(And(fDomain_eq_gDomain, Forall(x, fx_eq_gx, x_in_fDomain)), f_eq_g))

mappingAxioms.finish(locals())