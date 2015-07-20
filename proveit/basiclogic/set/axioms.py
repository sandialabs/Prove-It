from proveit.statement import Axioms
from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.multiExpression import Etcetera
from proveit.basiclogic import BOOLEANS, Forall, Exists, And, Or, Implies, Iff, Equals
from setOps import In, NotIn, Singleton, Union, Intersection, SubsetEq, SupersetEq, SetOfAll, EVERYTHING, NOTHING
from proveit.basiclogic.variables import x, y, A, B, C, S, f, P

etcC = Etcetera(C) # ..C..
fy = Operation(f, y) # f(y)
Py = Operation(P, y) # P(y)

setAxioms = Axioms(__package__)

inSetIsInBool = Forall((x, S), In(In(x, S), BOOLEANS))

# forall_{x, y} [x in Singleton(y)] = [x = y]
singletonDef = Forall((x, y), Equals(In(x, Singleton(y)), Equals(x, y)))

# forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
unionDef = Forall((x, A, B), Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B))))

# forall_{x, A, B} [x in (A intersection B)] <=> [(x in A) and (x in B)]
intersectionDef = Forall((x, A, B), Iff(In(x, Intersection(A, B)), And(In(x, A), In(x, B))))
        
# Composition of multi-Union, bypassing associativity for notational convenience:
# forall_{A, B, C} A union B union ..C.. = A union (B union ..C..)
unionComposition = Forall((A, B, C), Equals(Union(A, B, etcC), Union(A, Union(B, etcC))))

# Composition of multi-Intersection, bypassing associativity for notational convenience:
# forall_{A, B, ..C..} A intersect B intersect ..C.. = A intersect (B intersect ..C..)
intersectionComposition = Forall((A, B, C), Equals(Intersection(A, B, etcC), Intersection(A, Intersection(B, etcC))))
        
# forall_{A, B} [A subseteq B <=> (forall_{x in A} x in B)]
subsetDef = Forall((A, B), Iff(SubsetEq(A, B), Forall(x, In(x, B), In(x, A))))

# forall_{A, B} [A superseteq B <=> (forall_{x in B} x in A)]
supersetDef = Forall((A, B), Iff(SupersetEq(A, B), Forall(x, In(x, A), In(x, B))))

# forall_{P, f, x} [x in {f(y) | P(y)}] <=> [exists_{y | P(y)} x = f(y)]
setOfAllDef = Forall((P, f, x), Iff(In(x, SetOfAll(y, fy, conditions=Py)), Exists(y, Equals(x, fy), Py)))

# forall_{A, B} [forall_{x} x in A <=> x in B] => [A=B]
setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(In(x, A), In(x, B))), Equals(A, B)))

# forall_{x} x in EVERYTHING
allInEverything = Forall(x, In(x, EVERYTHING))

# forall_{x} x notin EVERYTHING
allNotInNothing = Forall(x, NotIn(x, NOTHING))

setAxioms.finish(locals())
