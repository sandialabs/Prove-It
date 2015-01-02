from proveItCore import *
from genericOperations import *
from booleans import Forall, Implies, And, Iff, compose, TRUE
from equality import Equals
from sets import In, sets, A, B, EVERYTHING

f = Variable('f')
g = Variable('g')
Q = Variable('Q')
x = Variable('x') 
y = Variable('y') 
fx = Operation(f, [x]) # f(x)
gx = Operation(g, [x]) # g(x)
Qx = Operation(Q, [x]) # Q(x)
fy = Operation(f, [y]) # f(y)
gy = Operation(g, [y]) # g(y)
Qy = Operation(Q, [y]) # Q(y)
fxMap = Lambda(x, fx) # x -> f(x)
fxGivenQxMap = Lambda(x, fx, Qx) # x -> f(x) | Q(x)
gxGivenQxMap = Lambda(x, gx, Qx) # x -> g(x) | Q(x)

mapping = Context('MAPPING')

DOMAIN = mapping.addLiteral('DOMAIN')
CODOMAIN = mapping.addLiteral('CODOMAIN')

class Domain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, DOMAIN, [mapExpr])
       
class CoDomain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, CODOMAIN, [mapExpr])

# forall_{f, Q} forall_{y | Q(y)} [x -> f(x) | Q(x)](y) = f(y)
mapping.mapApplication = mapping.stateAxiom(Forall((f, Q), Forall(y, Equals(Operation(fxGivenQxMap, y), fy), Qy)))

# forall_{f} [x -> f(x)] = [x -> f(x) | TRUE]
mapping.lambdaOverAllDef = mapping.stateAxiom(Forall(f, Equals(Lambda(x, fx), Lambda(x, fx, TRUE)))) 

# forall_{f, Q} forall_{y} y in Domain(x -> f(x) | Q(x)) <=> Q(y)
mapping.lambdaDomainDef = mapping.stateAxiom(Forall((f, Q), Forall(y, Iff(In(y, Domain(fxGivenQxMap)), Qy))))

# forall_{f, g} [Domain(f) = Domain(g) and forall_{x in Domain(f)} f(x) = g(x)] => (f = g)}
fDomain_eq_gDomain = Equals(Domain(f), Domain(g)) # Domain(f) = Domain(g)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
x_in_fDomain = In(x, Domain(f)) # x in Domain(f)
f_eq_g = Equals(f, g) # f = g
mapping.mapIsAsMapDoes = mapping.stateAxiom(Forall((f, g), Implies(And(fDomain_eq_gDomain, Forall(x, fx_eq_gx, x_in_fDomain)), f_eq_g)))


# forall_{f, g, Q} Domain(x -> f(x) | Q(x)) = Domain(x -> g(x) | Q(x)) 
def lambdaDomainEqualityDerivation():
    # y in Domain(x -> f(x) | Q(x)) <=> Q(y)
    y_in_fmap_iff_Qy = mapping.lambdaDomainDef.specialize().specialize().prove()
    # y in Domain(x -> g(x) | Q(x)) <=> Q(y)
    y_in_gmap_iff_Qy = mapping.lambdaDomainDef.specialize({f:g}).specialize().prove()
    # forall_{x} x in Domain(x -> f(x) | Q(x)) <=> x in Domain(x -> g(x) | Q(x))
    y_in_fmap_iff_y_in_gmap = y_in_fmap_iff_Qy.applyTransitivity(y_in_gmap_iff_Qy).generalize(y).prove()
    # forall_{f, g, Q} Domain(x -> f(x) | Q(x)) = Domain(x -> g(x) | Q(x)) 
    return sets.setIsAsSetContains.specialize({x:y, A:Domain(fxGivenQxMap), B:Domain(gxGivenQxMap)}).deriveConclusion().generalize((f, g, Q)).qed()
mapping.deriveOnDemand('lambdaDomainEquality', lambdaDomainEqualityDerivation)

"""
# forall_{f, g} Domain(x -> f(x)) = Domain(x -> g(x)) 
def lambdaOverAllDomainEqualityDerivation():
    # Domain(x -> f(x)) = EVERYTHING
    fmap_domain_eq_everything = mapping.lambdaOverAllDomainDef.specialize().prove()
    # Domain(x -> g(x)) = EVERYTHING
    gmap_domain_eq_everything = mapping.lambdaOverAllDomainDef.specialize({f:g}).prove()
    # forall_{f, g} Domain(x -> f(x)) = Domain(x -> g(x))
    return fmap_domain_eq_everything.applyTransitivity(gmap_domain_eq_everything).generalize([f, g]).qed()
mapping.deriveOnDemand('lambdaOverAllDomainEquality', lambdaOverAllDomainEqualityDerivation)
"""

# forall_{f, g, Q} {forall_{x | Q(x)} [f(x) = g(x)]} => {[y -> f(y) | Q(y)] = [y -> g(y) | Q(y)]
def mapSubstitionDerivation():
    fyGivenQyMap = Lambda([y], fy, [Qy]) # x -> f(x) | Q(x)
    gyGivenQyMap = Lambda([y], gy, [Qy]) # x -> g(x) | Q(x)
    # hypothesis = forall_{x | Q(x)} [f(x) = g(x)]
    hypothesis = Forall([x], fx_eq_gx, [Qx])
    # [y -> f(y) | Q(y)](x) = f(x), assuming Q(x)
    fmap_x_eq_fx = mapping.mapApplication.specialize().specialize({x:y, y:x}).prove({Qx})
    # [y -> g(y) | Q(y)](x) = g(x), assuming Q(x)
    gmap_x_eq_gx = mapping.mapApplication.specialize({f:g}).specialize({x:y, y:x}).prove({Qx})
    # [y -> f(y) | Q(y)](x) = g(x), assuming hypothesis, Q(x)
    fmap_x_eq_gx = fmap_x_eq_fx.applyTransitivity(hypothesis.specialize()).prove({hypothesis, Qx})
    # [y -> f(y) | Q(y)](x) = [y -> g(y) | Q(y)](x), assuming hypothesis, Q(x)
    fmap_x_eq_g_map_x = fmap_x_eq_gx.applyTransitivity(gmap_x_eq_gx).prove({hypothesis, Qx})
    # [x in Domain(y -> f(y) | Q(y))] => Q(x)
    mapping.lambdaDomainDef.specialize().specialize({x:y, y:x}).deriveRightImplication().prove(Qx)
    # forall_{x in Domain([y -> f(y) | Q(y)])} [y -> f(y) | Q(y)](x) = [y -> g(y) | Q(y)](x), assumping hypothesis
    same_map_under_domain = fmap_x_eq_g_map_x.generalize(x, In(x, Domain(Lambda(y, fy, Qy)))).prove({hypothesis})
    # Domain(y -> f(y) | Q(y)) = Domain(y -> g(y) | Q(y))
    domain_equality = mapping.lambdaDomainEquality.specialize({x:y}).prove()
    # Domain(y -> f(y) | Q(y)) = Domain(y -> g(y) | Q(y)) and forall_{x in Domain([y -> f(y) | Q(y)])} [y -> f(y) | Q(y)](x) = [y -> g(y) | Q(y)](x), assumping hypothesis
    compose(domain_equality, same_map_under_domain).prove({hypothesis})
    # {forall_{x | Q(x)} [f(x) = g(x)]} => {[y -> f(y) | Q(y)] = [y -> g(y) | Q(y)]
    return Implies(hypothesis, mapping.mapIsAsMapDoes.specialize({f:fyGivenQyMap, g:gyGivenQyMap}).deriveConclusion()).generalize([f, g, Q]).qed()    
mapping.deriveOnDemand('mapSubstitution', mapSubstitionDerivation)

# forall_{f, g} {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
def mapOverAllSubstitionDerivation():
    # hypothesis = forall_{x} [f(x) = g(x)]
    hypothesis = Forall([x], fx_eq_gx)
    # forall_{x | TRUE} [f(x) = g(x)] assuming hypothesis
    hypothesis.specialize().generalize([x], [TRUE]).prove({hypothesis})
    # {[y -> f(y) | TRUE] = [y -> g(y) | TRUE] assuming hypothesis
    fmap_given_T_eq_gmap_given_T = mapping.mapSubstitution.specialize({Qx:TRUE}).deriveConclusion().prove({hypothesis})
    # [y -> f(y)] = [y -> g(y) | TRUE] assuming hypothesis
    fmap_eq_gmap_given_T = mapping.lambdaOverAllDef.specialize({x:y}).applyTransitivity(fmap_given_T_eq_gmap_given_T).prove({hypothesis})
    # [y -> f(y)] = [y -> g(y)] assuming hypothesis
    fmap_eq_gmap = mapping.lambdaOverAllDef.specialize({f:g, x:y}).applyTransitivity(fmap_eq_gmap_given_T).prove({hypothesis})
    # {forall_{x} [f(x) = g(x)]} => {[y -> f(y)] = [y -> g(y)]
    return Implies(hypothesis, fmap_eq_gmap).generalize([f, g]).qed()
mapping.deriveOnDemand('mapOverAllSubstitution', mapOverAllSubstitionDerivation)
    
    