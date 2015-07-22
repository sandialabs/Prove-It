from proveit.statement import Axioms
from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.multiExpression import Etcetera
from proveit.basiclogic import BOOLEANS, Forall, Exists, And, Or, Implies, Iff, Equals
from setOps import In, NotIn, Singleton, Union, Intersection, SubsetEq, SupersetEq, SetOfAll, EVERYTHING, NOTHING
from proveit.common import x, y, z, A, B, C, S, f, P, Cetc, xEtc, zEtc, fy, Py

setAxioms = Axioms(__package__, locals())

# forall_{..x.., y, ..z.., S} [..x.., y, ..z.. in S] => (y in S)
multiInImpliesEachIn = Forall((xEtc, y, zEtc, S), Implies(In([xEtc, y, zEtc], S), In(y, S)))

# forall_{..x.., y, S} [(..x.. in S) and (y in S)] => (..x.., y in S)
multiInComposition = Forall((xEtc, y, S), Implies(And(In(xEtc, S), In(y, S)), In([xEtc, y], S)))

# forall_{..x.., S} [..x.. in S] in BOOLEANS
inSetIsInBool = Forall((xEtc, S), In(In(xEtc, S), BOOLEANS))

# forall_{x, y} [x in Singleton(y)] = [x = y]
singletonDef = Forall((x, y), Equals(In(x, Singleton(y)), Equals(x, y)))

# forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
unionDef = Forall((x, A, B), Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B))))

# forall_{x, A, B} [x in (A intersection B)] <=> [(x in A) and (x in B)]
intersectionDef = Forall((x, A, B), Iff(In(x, Intersection(A, B)), And(In(x, A), In(x, B))))
        
# Composition of multi-Union, bypassing associativity for notational convenience:
# forall_{A, B, ..C..} A union B union ..C.. = A union (B union ..C..)
unionComposition = Forall((A, B, Cetc), Equals(Union(A, B, Cetc), Union(A, Union(B, Cetc))))

# Composition of multi-Intersection, bypassing associativity for notational convenience:
# forall_{A, B, ..C..} A intersect B intersect ..C.. = A intersect (B intersect ..C..)
intersectionComposition = Forall((A, B, Cetc), Equals(Intersection(A, B, Cetc), Intersection(A, Intersection(B, Cetc))))
        
# forall_{A, B} [A subseteq B <=> (forall_{x in A} x in B)]
subsetDef = Forall((A, B), Iff(SubsetEq(A, B), Forall(x, In(x, B), A)))

# forall_{A, B} [A superseteq B <=> (forall_{x in B} x in A)]
supersetDef = Forall((A, B), Iff(SupersetEq(A, B), Forall(x, In(x, A), B)))

# forall_{P, f, x} [x in {f(y) | P(y)}] <=> [exists_{y | P(y)} x = f(y)]
setOfAllDef = Forall((P, f, x), Iff(In(x, SetOfAll(y, fy, conditions=Py)), Exists(y, Equals(x, fy), conditions=Py)))

# forall_{A, B} [forall_{x} x in A <=> x in B] => [A=B]
setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(In(x, A), In(x, B))), Equals(A, B)))

# forall_{x} x in EVERYTHING
allInEverything = Forall(x, In(x, EVERYTHING))

# forall_{x} x notin EVERYTHING
allNotInNothing = Forall(x, NotIn(x, NOTHING))

setAxioms.finish(locals())
