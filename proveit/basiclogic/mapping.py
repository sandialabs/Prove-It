import sys
from proveit.statement import *
from proveit.context import Context
from proveit.basiclogic import *
from variables import *

literals = Literals()
DOMAIN = literals.add('DOMAIN')
CODOMAIN = literals.add('CODOMAIN')

def _defineAxioms():
    # forall_{f, Q} forall_{y | Q(y)} [x -> f(x) | Q(x)](y) = f(y)
    _firstAxiom =\
    mapApplication = Forall((f, Q), Forall(y, Equals(Operation(fxGivenQxMap, y), fy), Qy))
    
    # forall_{f} [x -> f(x)] = [x -> f(x) | TRUE]
    lambdaOverAllDef = Forall(f, Equals(Lambda(x, fx), Lambda(x, fx, TRUE)))
    
    # forall_{f, Q} forall_{y} y in Domain(x -> f(x) | Q(x)) <=> Q(y)
    lambdaDomainDef = Forall((f, Q), Forall(y, Iff(In(y, Domain(fxGivenQxMap)), Qy)))
    
    # forall_{f, g} [Domain(f) = Domain(g) and forall_{x in Domain(f)} f(x) = g(x)] => (f = g)}
    _fDomain_eq_gDomain = Equals(Domain(f), Domain(g)) # Domain(f) = Domain(g)
    _fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
    _x_in_fDomain = In(x, Domain(f)) # x in Domain(f)
    _f_eq_g = Equals(f, g) # f = g
    mapIsAsMapDoes = Forall((f, g), Implies(And(_fDomain_eq_gDomain, Forall(x, _fx_eq_gx, _x_in_fDomain)), _f_eq_g))
    
    return _firstAxiom, locals()

fx_eq_gx = Equals(fx, gx)

def _defineTheorems():
    # forall_{f, g, Q} Domain((x | Q(x) -> f(x)) = Domain(x -> g(x) | Q(x)) ]
    _firstTheorem =\
    lambdaDomainEquality = Forall((f, g, Q), Equals(Domain(Lambda(x, fx, Qx)), Domain(Lambda(x, gx, Qx))))
    
    # forall_{f, g, Q} {forall_{x | Q(x)} [f(x) = g(x)]} => {[(y | Q(y)) -> f(y)] = [(y | Q(y)) -> g(y)]
    mapSubstitution = Forall((f, g, Q), Implies(Forall(x, fx_eq_gx, Qx), Equals(Lambda(y, fy, Qy), Lambda(y, gy, Qy))))
    
    # forall_{f, g} {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
    mapOverAllSubstition = Forall((f, g), Implies(Forall(x, fx_eq_gx), Equals(Lambda(y, fy), Lambda(y, gy))))

    return _firstTheorem, locals()
    
mapping = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)


class Domain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, DOMAIN, [mapExpr])
       
class CoDomain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, CODOMAIN, [mapExpr])

