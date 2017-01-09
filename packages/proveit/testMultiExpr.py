from proveit.multiExpression import ExpressionList, Etcetera,\
    singleOrMultiExpression
from proveit.expression import *
from proveit.statement import ImproperSpecialization
from proveit.basiclogic.boolean.quantifiers import Forall
x = Variable('x')
y = Variable('y')
Q = Variable('Q')
P = Variable('P')
A = Variable('A')
R = Variable('R')
S = Variable('S')
y = Variable('y')
z = Variable('z')
Aetc = Etcetera(A)
Qetc = Etcetera(Q)
etcP = Etcetera(P)
xEtc = Etcetera(x)
yEtc = Etcetera(y)

def specToStr(spec):
    return '{' + ', '.join(str(key) + ' : ' + singleOrMultiExpression(val).formatted(LATEX) for key, val in spec.iteritems()) + '}'

expr = Forall((Qetc, P, A), Forall(xEtc, Operation(P, ExpressionList(xEtc, A)), Etcetera(Operation(Q, xEtc))))
print "\nInitial expression:"
print expr.formatted(LATEX)

spec = {Qetc: [R, S]}
print "\nRelabeling via ", specToStr(spec), ':'
print expr.relabel(spec).formatted(LATEX)

spec = {A: Aetc}
print "\nSpecializing via ", specToStr(spec), ':'
try:
    print expr.specialize(spec).formatted(LATEX)
except ImproperSpecialization as e:
    print "Gives anticipated ImproperSpecialization exception: " + e.message
except Exception as e:
    print "Unexpected error"
    raise e

spec = {xEtc: x}
print "\nRelabeling via ", specToStr(spec), ':'
print expr.relabel(spec).formatted(LATEX)
    
spec = {Etcetera(Operation(Q, xEtc)): Operation(R, xEtc)}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec).formatted(LATEX)

spec = {Etcetera(Operation(Q, xEtc)): [Operation(R, xEtc), Operation(S, xEtc)]}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec).formatted(LATEX)

spec = {Qetc: [R, S]}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec).formatted(LATEX)

spec = {P: [R, S]}
print "\nSpecializing via ", specToStr(spec), ':'
try:
    print expr.specialize(spec)
    print "Should have raised an ImproperSpecialization"
except ImproperSpecialization as e:
    print "Gives anticipated ImproperSpecialization exception: " + e.message
except Exception as e:
    print "Unexpected error"
    raise e

spec = {xEtc:[y, z], Etcetera(Operation(Q, [y, z])): [Operation(R, y), Operation(S, z)]}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec)

spec = {xEtc:[xEtc, yEtc], Etcetera(Operation(Q, [xEtc, yEtc])): [Etcetera(Operation(Q, xEtc)), Etcetera(Operation(R, yEtc))]}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec)

spec = {xEtc:[y, z], P:y}
print "\nSpecializing via ", specToStr(spec), ':'
try:
    print expr.specialize(spec)
    print "Should have raised a ScopingViolation"
except ScopingViolation as e:
    print "Gives anticipated ScopingViolation exception: " + e.message
except Exception as e:
    print "Unexpected error"
    raise e

spec = {xEtc:P}
print "\nSpecializing via ", specToStr(spec), ':'
try:
    print expr.specialize(spec)
    print "Should have raised a ScopingViolation"
except ScopingViolation as e:
    print "Gives anticipated ScopingViolation exception: " + e.message
except Exception as e:
    raise e

# proveit.FORALL([(..\x..)->{'instance_expression':\P(..\x..), 'conditions':..\Q(..\x..)..}])
# proveit.FORALL([(..\x..)->{'instance_expression':\P(..\x..), 'conditions':..\Q(..\x..)..}])
# ['..\\Q..:[(..\\x..)->\\R(..\\x..)]']
