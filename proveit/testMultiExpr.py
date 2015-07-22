from proveit.multiExpression import ExpressionList, Etcetera,\
    singleOrMultiExpression
from proveit.expression import *
from proveit.statement import ImproperSpecialization
from proveit.basiclogic.boolean.quantifiers import Forall
x = Variable('x')
y = Variable('y')
Q = Variable('Q')
P = Variable('P')
etcQ = Etcetera(Q)
etcP = Etcetera(P)
xEtc = Etcetera(x)
yEtc = Etcetera(y)
R = Variable('R')
S = Variable('S')
y = Variable('y')
z = Variable('z')

def specToStr(spec):
    return '{' + ', '.join(str(key) + ' : ' + singleOrMultiExpression(val).formatted(LATEX) for key, val in spec.iteritems()) + '}'

expr = Forall(P, Forall(etcQ, Forall(xEtc, Operation(P, xEtc), Etcetera(Operation(Q, xEtc)))))
print "Initial expression:"
print expr.formatted(LATEX)

spec = {etcQ: [R, S]}
print "\Relabeling via ", specToStr(spec), ':'
print expr.relabel(spec).formatted(LATEX)

spec = {P: etcP}
print "\nSpecializing via ", specToStr(spec), ':'
print 'SHOULD NOT BE ALLOWED'
print expr.specialize(spec).formatted(LATEX)

expr = Forall((etcQ, P), Forall(xEtc, Operation(P, xEtc), Etcetera(Operation(Q, xEtc))))
print "\nInitial expression:"
print expr.formatted(LATEX)
    
spec = {Etcetera(Operation(Q, xEtc)): Operation(R, xEtc)}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec).formatted(LATEX)

spec = {Etcetera(Operation(Q, xEtc)): [Operation(R, xEtc), Operation(S, xEtc)]}
print "\nSpecializing via ", specToStr(spec), ':'
print expr.specialize(spec).formatted(LATEX)

spec = {etcQ: [R, S]}
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
