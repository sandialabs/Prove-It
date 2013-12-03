from basicLogic import *

sets = Context('SETS')

prevContext = Context.current
Context.current = sets

S = Variable('S')
P = Variable('P')
x = Variable('x')
Px = Operation(P, [x])


# Axioms related to sets that weren't introduced in basicLogic

# forall_{A, B} [A subset B => (forall_{x} x in A => x in B)]
subsetDef = sets.stateAxiom(Forall([A, B], Implies(Subset(A, B), Forall([x], Implies(In(x, A), In(x, B))))))

# forall_{A, B} [A superset B => (forall_{x} x in B => x in A)]
supersetDef = sets.stateAxiom(Forall([A, B], Implies(Superset(A, B), Forall([x], Implies(In(x, B), In(x, A))))))

# forall_{P, x} {[x in {y | P(y)}] <=> P(x)}
setOfAllDef = sets.stateAxiom(Forall([P, x], Iff(In(x, SetOfAll([y], y, suchThat=[Py])), Px)))

"""
# forall_{x, y} [x in Singleton(y)] <=> [x = y]
singletonDef = sets.stateAxiom(Forall([x, y], Iff(In(x, Singleton(y)), Equals(x, y))))

# forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
unionDef = sets.stateAxiom(Forall([x, A, B], Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B)))))

# forall_{x, A, B} [x in (A intersection B)] <=> [(x in A) and (x in B)]
intersectionDef = sets.stateAxiom(Forall([x, A, B], Iff(In(x, Intersection(A, B)), And(In(x, A), In(x, B)))))

# forall_{x} x in EVERYTHING
everythingDef = sets.stateAxiom(Forall([x], In(x, EVERYTHING)))

# forall_{x} not(x in NOTHING)
nothingDef = sets.stateAxiom(Forall([x], Not(In(x, NOTHING))))

# forall_{S} S union Complement(S) = EVERTHING
complementCompletion = sets.stateAxiom(Forall([S], Equals(Union(S, Complement(S)), EVERYTHING)))
                  
# forall_{S} S intersection Complement(S) = NOTHING
complementExclusion = sets.stateAxiom(Forall([S], Equals(Intersection(S, Complement(S)), NOTHING)))

# forall_{A, B} [A subseteq B => (forall_{x in A} x in B)]
subsetEqDef = sets.stateAxiom(Forall([A, B], Implies(SubsetEq(A, B), Forall([(x, A)], In(x, B)))))

# forall_{x, a, Q, S} {x in [union_{a | Q(a)} S(a)] <=> exists_{a | Q(a)} [x in S(a)]}   
unionOfSetsDef = sets.stateAxiom(Forall([x, a, Q, S], Iff(In(x, UnionOfSets([a], Sa, [Qa])), Exists([a], In(x, Sa), [Qa]))))
        
# forall_{A, B} {[forall_{x in A} P(x) and forall_{x in B} P(x)] => forall_{x in (A union B)} P(x)}
def forallDomainUnificationDerivation():
    # hypothesis: forall_{x in A} P(x) and forall_{x in B} P(x)
    hypothesis = sets.state(And(Forall([(x, A)], Px), Forall([(x, B)], Px)))
    # [x in A => P(x)] given hypothesis
    xInA_impl_Px = hypothesis.deriveLeft().domainElimination().specialize()
    # [x in B => P(x)] given hypothesis
    xInB_impl_Px = hypothesis.deriveRight().domainElimination().specialize()
    # x in A => P(x) and x in B => P(x) given hypothesis
    compose(xInA_impl_Px, xInB_impl_Px)
    # [x in A => P(x) and x in B => P(x)] => [(x in A or x in B) => P(x)]
    hypotheticalDisjunction.specialize({A:In(x, A), B:In(x, B), C:Px})
    # [x in (A union B)] => [(x in A) or (x in B)]
    unionDef.specialize().deriveRightImplication()
    # forall_{x in (A union B)} Px given forall_{x in A} P(x) and forall_{x in B} P(x)
    conclusion = hypotheticallyReason(Implies(In(x, Union(A, B)), Px), assumptions={hypothesis}).generalize([x], [In(x, Union(A, B))])
    # forall_{A, B} {[forall_{x in A} P(x) and forall_{x in B} P(x)] => forall_{x in (A union B)} P(x)}
    return hypotheticallyReason(Implies(hypothesis, conclusion)).generalize([A, B]).prove()
forallDomainUnification = forallDomainUnificationDerivation()

# forall_{a} [P(a) => forall_{x in {a}} P(x}]
def forallIntroductionDerivation():
    # P(x), given P(a) and (x=a)
    substitute(Equals(x, a).deriveReversed(), Function(Px, [x]))
    # x in {a} => (x = a)
    singletonDef.specialize({x:x, y:a}).deriveRightImplication()
    # forall_{x in {a}} P(x), given P(a)
    conclusion = hypotheticallyReason(Implies(In(x, Singleton(a)), Px), assumptions={Pa}).generalize([x], [In(x, Singleton(a))])
    return hypotheticallyReason(Implies(Pa, conclusion)).generalize([a]).prove()
forallIntroduction = forallIntroductionDerivation()

# forall_{a, b} {P(a) and P(b)] => forall_{x in ({a} union {b})} P(x)}
def forallBinaryUnificationDerivation():
    # hypothesis: P(a) and forall_{x in B} P(x)
    hypothesis = sets.state(And(Pa, Pb))
    # P(a), P(b) given hypothesis
    hypothesis.deriveEach()
    # [forall_{x in {a}} P(x) and forall_{x in {b}} P(x)] given hypothesis
    compose(forallIntroduction.specialize({a:a}).deriveConclusion(), forallIntroduction.specialize({a:b}).deriveConclusion())
    # forall_{x in ({a} union {b})} P(x)} given hypothesis
    conclusion = forallDomainUnification.specialize({A:Singleton(a), B:Singleton(b)}).deriveConclusion()
    return hypotheticallyReason(Implies(hypothesis, conclusion)).generalize([a, b]).prove()
forallBinaryUnification = forallBinaryUnificationDerivation()

# forall_{a, B} {P(a) and forall_{x in B} P(x)] => forall_{x in ({a} union B)} P(x)}
def forallDomainAddMemberDerivation():
    # hypothesis: P(a) and forall_{x in B} P(x)
    hypothesis = sets.state(And(Pa, Forall([(x, B)], Px)))
    # P(A), forall_{x in B} P(x) given hypothesis
    hypothesis.deriveEach()
    # [forall_{x in {a}} P(x) and forall_{x in B} P(x) given hypothesis
    compose(forallIntroduction.specialize().deriveConclusion(), Forall([(x, B)], Px))
    # forall_{x in ({a} union B)} P(x)} given hypothesis
    conclusion = forallDomainUnification.specialize({A:Singleton(a), B:B}).deriveConclusion()
    return hypotheticallyReason(Implies(hypothesis, conclusion)).generalize([a, B]).prove()
forallDomainAddMember = forallDomainAddMemberDerivation()

# forall_{x, S} (x in S) or (x in Complement(S))
def inSetOrInComplementDerivation():
    # S union Complement(S) = EVERTHING
    setUnionComplement_equal_Everything = complementCompletion.specialize()
    # x in EVERYTHING
    everythingDef.specialize()
    # x in [S union Complement(S)]
    substitute(setUnionComplement_equal_Everything.deriveReversed(), Function(In(x, X), [X]))
    # (x in S) or (x in Complement(S))
    return unionDef.specialize({A:S, B:Complement(S)}).deriveRight().generalize([x, S])
inSetOrInComplement = inSetOrInComplementDerivation()


# forall_{x, y} Not(x=y) => x in Complement({y})
def inComplementIfNotEqualDerivation():
    # hypothesis: Not(x=y)
    hypothesis = NotEquals(x, y)
    # {(x in {y}) or (x in Complement({y}))
    xInY_or_xInCy = inSetOrInComplement.specialize({S:Singleton(y)})
    # (x in {y}) => (x = y)
    singletonDef.specialize().deriveRight()
    # (x=y)=FALSE given hypothesis
    xIsY_eq_F = hypothesis.equateNegatedToFalse()
    # Not((x=y)=TRUE) given hypothesis (and Not(FALSE=TRUE))
    substitute(xIsY_eq_F.deriveReversed(), Function(NotEquals(X, TRUE), [X]))
    # [Not((x=y)=TRUE) => Not((x in {y})=TRUE)] 
    notEq_impl_notIn = transposition.specialize({A:In(x, Singleton(y)), B:Equals(x, y)}).deriveConclusion()
    # Not((x in {y})=TRUE)] and [{(x in {y}) or (x in Complement({y}))], given hypothesis
    compose(notEq_impl_notIn.deriveConclusion(), xInY_or_xInCy)    
    # x in Complement(y), given hypothesis
    conclusion = orImpliesRightDerivation().specialize({A:xInY_or_xInCy.operands[0], B:xInY_or_xInCy.operands[1]}).deriveConclusion()
    # Not(x=y) => x in Complement({y})
    return hypotheticallyReason(Implies(hypothesis, conclusion)).generalize([x, y]).prove()
inComplementIfNotEqual = inComplementIfNotEqualDerivation()



# a in {b | Q(b)} <=> Q(a)
def inSetOfAllIffConditionMetDerivation():
    # lhs = a in {b | Q(b)}.  {b | Q(b)} is shorthand for union of singleton sets.
    lhs = In(a, UnionOfSets([b], Singleton(b), [Qb]))
    # a in {b | Q(b)} <=> exists_{b | Q(b)} [a in {b}]}   
    unionOfSingletonsByDef = unionOfSetsDef.specialize({x:a, a:b, S:Function(Singleton(a), [a])})
    # [a in {b}] = [a = b] 
    equivBySingletonDef = ...
    # a in {b | Q(b)} <=> exists_{b | Q(b)} [a = b]}   
    substitute(equivBySingletonDef, Function(Iff(lhs, Exists([b], X, [Qb])), [X]))
    # exists_{b | Q(b)} [a = b]} <=> Q(a)
    
    unionOfSingletonsByDef
    rhs = Qa
    
inSetOfAllIffConditionMet = inSetOfAllIffConditionMetDerivation()
"""

Context.current = prevContext
