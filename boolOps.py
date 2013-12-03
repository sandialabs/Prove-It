from proveItCore import *
from genericOperations import *

booleans = Context('BOOLEANS')

# boolean related literals
IMPLIES = booleans.addLiteral('IMPLIES')
IFF = booleans.addLiteral('IFF')
TRUE = booleans.addLiteral('TRUE', {MATHML:'<mstyle mathvariant="normal"><mi>true</mi></mstyle>'})
FALSE = booleans.addLiteral('FALSE', {MATHML:'<mstyle mathvariant="normal"><mi>false</mi></mstyle>'})
NOT = booleans.addLiteral('NOT')
AND = booleans.addLiteral('AND')
OR = booleans.addLiteral('OR')
BOOLEANS = booleans.addLiteral('BOOLEANS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x1D539;</mtext><mspace/></mstyle>'})
FORALL = AND # a generalization of AND
EXISTS = OR # a generalization of OR

class Forall(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Nest Forall OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, FORALL, lambda iVars, iExpr, conds: Forall(iVars, iExpr, conds), instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'forall'
        elif formatType == MATHML:
            return '<mo>&#x2200;</mo>'

    def implicitInstanceVar(self):
        '''
        If the condition is that the instance variable is in some set, then
        the instance variable is implicit (stating the condition indicates
        the instance variable).
        '''
        from setOps import In
        return self.condition != None and isinstance(self.condition, In) and self.condition.element == self.instanceVar

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == FORALL:
            return Forall([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)
    
    """
    def domainElimination(self):
        '''
        Derive forall_{x} Q(x) => P(x) from something of the form
        forall_{x | Q(x)} P(x).
        '''
        return forallSuchThatDef.specialize({x:self.instanceVar, P:Function(self.instanceExpression, [self.instanceVar]), Q:Function(self.condition, [self.instanceVar])}).deriveRight()
    """
    """
    def specialize(self, subMap=None):
        '''
        This makes a specialization of this expression, eliminating Forall 
        operations according to the given substitution map that may introduce 
        'arbitrary' free variables.  This overrides the Expression version
        to treat arbitrary conditions by introducing hypotheses for the conditions.
        '''
        if self.condition == None:
            # deal with the None condition and then recurse on whatever remains
            innerExpr = self
            outerSubMap = SubstitutionMap()
            innerSubMap = SubstitutionMap(subMap)
            while isinstance(innerExpr, OperationOverInstances) and innerExpr.operator == FORALL and innerExpr.condition == None:
                if innerExpr.instanceVar in innerSubMap:
                    outerSubMap[innerExpr.instanceVar] = innerSubMap.pop(innerExpr.instanceVar)
                innerExpr = innerExpr.instanceExpression
            # relabel inner variable to safe dummy variables
            for innerVar in innerSubMap.keys():
                outerSubMap[innerVar] = safeDummyVar([innerExpr] + outerSubMap.values())
            innerSubMap = {outerSubMap[v] : innerSubMap[v] for v in innerSubMap.keys()}
            if innerExpr.operator == FORALL:
                # recurse for the inner FORALL and use the Expression version for the outer
                return Expression.specialize(self, outerSubMap).specialize(innerSubMap)
            else:
                # just use the Expression version now
                return Expression.specialize(self, subMap)
        # forall_{x} Q(x) => P(x) from forall_{x | Q(x)} P(x)
        noConditionForall = self.domainElimination()
        curSubMap = SubstitutionMap()
        innerSubMap = subMap
        if subMap != None and self.instanceVar in subMap:
            curSubMap[self.instanceVar] = subMap[self.instanceVar]
            innerSubMap = subMap.copy()
            innerSubMap.pop(self.instanceVar)
        # specialize 'x', derive the conclusion of Q(x) => P(x), and then recurse on P(x) if necessary
        curSpecialized = noConditionForall.specialize(curSubMap).deriveConclusion()
        if isinstance(curSpecialized, Forall):
            # recurse
            return curSpecialized.specialize(innerSubMap)
        return curSpecialized
    """

    def proveByCases(self, conditionSplitter, proveCase=None):
        '''
        '''
        if self.statement == None:
            Context.current.state(self)
        if self.wasProven():
            return True # Already known to be true, so we are done before we started
        conditions = []
        expr = self
        while isinstance(expr, Forall):
            if expr.condition != None:
                conditions.append(expr.condition)
            expr = expr.instanceExpression
        conditionSplits = [conditionSplitter(condition) for condition in conditions]
        conditionCases = itertools.product(*conditionSplits)

    
    """
    def proveByCases(self, conditionSplitter, proveCase=None):
        '''
        Prove that this Forall statement expression is true given certain prerequisites, 
        by iterating over pairs of domain splits for instance variables of any number of 
        sequentially nested Forall expressions.  One kind of prerequisite is that the domain
        splits in domainSplits are proper splits for the corresponding domain: domain = A union B.
        The other kind of prerequisite is that each case instance is true.  If provided,
        the proveCase method can assist with this, taking, as it's argument, the case to 
        prove.  Returns true if the proof succeeds (otherwise some prerequisites may need to be
        fulfilled).
        See DomainSplits in boolsSet.
        '''
        from sets import Singleton
        if self.statement == None:
            Context.current.state(self)
        if self.isProven():
            return True # Already known to be true, so we are done before we started
        poppedInstanceVar = False
        if self.instanceVar in domainSplits:
            # domain split specified via the instance variable
            subA, subB = domainSplits.pop(self.instanceVar)
            poppedInstanceVar = True
        elif self.domain in domainSplits:
            # domain split specified via the domain
            subA, subB = domainSplits.get(self.domain)       
        else:
            # no applicable domain split -- prove as a case if possible
            if proveCase != None and not self.isProven():
                proveCase(self)
            return self.isProven()
        def makeCase(domain):
            if isinstance(domain, Singleton):
                # for singleton sub-domain, the case is just the instance expression with the proper substitution
                subMap = SubstitutionMap({self.instanceVar:domain.elem})
                return Context.current.state(self.instanceExpression.substituted(subMap))
            else:
                # non-singleton sub-domain
                return Context.current.state(Forall([(self.instanceVar, domain)], self.instanceExpression))
        caseA, caseB = [makeCase(domain) for domain in (subA, subB)]
        # must recurse for each case
        for case in (caseA, caseB):
            print "case", case
            if isinstance(case, Forall):
                case.proveByCases(domainSplits, proveCase)
            elif proveCase != None and not case.isProven():
                proveCase(case)
            print "proven? ", case.isProven()
        if poppedInstanceVar:
            domainSplits.specifyVarSplits(self.instanceVar, subA, subB) # add it back in
        # compose the cases into [caseA and caseB]
        compose(caseA, caseB) 
        # unify the cases into a "forall" over the entire domain
        domainSplits.unify(self.domain, subA, subB, Function(self.instanceExpression, [self.instanceVar]))
        return self.isProven()
    """
"""        
    def equateSingletonInstance(self):
        '''
        Assuming the domain of this Forall statement expression is a Singleton, forall_{x in {E}} P{x},
        equate it with P{E}, and return P{E}.
        '''
        
        # WOULD BE BETTER (MORE ELEGANT) TO DERIVE A THEOREM AND APPLY IT HERE:
        # forall_{P, E} [(forall_{x in {E}} P{x}) <=> P{E}]
        from sets import singletonDef, A, B, P, x, y
        from basicLogic import Implies, Equals, substitutionAxiom, substitute
        assert isinstance(self.domain, Singleton)
        # Equate forall_{x in {E}} P{x} and forall_{x} x in {E} => P{x}
        self.equateForallEverything(1)
        opArg = self.instanceExpression.safeDummyVar()
        P_opArg = Forall([self.instanceVar], Implies(opArg, self.instanceExpression))
        # Equate forall_{x} x in {E} => P{x} and forall_{x} x = E => P{x}
        singletonEquivalence = Equals(In(self.instanceVar, self.domain), Equals(self.instanceVar, self.domain.elem))
        substitute(singletonEquivalence, P_opArg, opArg)
        substitute(singletonEquivalence.reversed(), P_opArg, opArg)
        # Equate forall_{x} x=E => P{x} and P{E}
        # First P{E} => [forall_{x} x=E => P{x}]
        subMap = SubstitutionMap({x:self.domain.elem, y:self.instanceVar})
        subMap.substituteOp(P, P_opArg, [opArg])
        substitutionAxiom.deriveInstance(subMap, [], [self.instanceVar])
        # TODO: derive
        return P_opArg.substituted({opArg, self.domain.elem})
"""

class Exists(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Nest Exists OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.  For convenience, conditions of the form 
        In(instanceVar, domain) may be provided implicitly via tuples in the instanceVars collection.  
        For example, instanceVars=[(a, A), (b, B)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, A), In(b, B)].  You can also provide multiple instance variables per domain 
        as in the following: instanceVars=[([a, b], S)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, S), In(b, S)].  These implicit conditions are prepended to any explicitly 
        given conditions as this is processed.
        '''
        NestableOperationOverInstances.__init__(self, EXISTS, lambda iVars, iExpr, conds: Exists(iVars, iExpr, conds), instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'exist'
        elif formatType == MATHML:
            return '<mo>&#x2203;</mo>'

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == EXISTS:
            return Exists([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)
        

class Implies(BinaryOperation):
    def __init__(self, hypothesis, conclusion):
        BinaryOperation.__init__(self, IMPLIES, hypothesis, conclusion)
        self.hypothesis = hypothesis
        self.conclusion = conclusion

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '=>'
        elif formatType == MATHML:
            return '<mo>&#x21D2;</mo>'

    def remake(self, operator, operands):
        if operator == IMPLIES and len(operands) == 2:
            return Implies(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

    def deriveConclusion(self):
        '''
        State and return the conclusion which derives from this implication.
        '''
        return Context.current.state(self.conclusion)
                
    def applySyllogism(self, otherImpl):
        '''
        From A=>B (self) and B=>C (otherImpl) return A=>C which derives
        from A=>B and B=>C via hypothetical reasoning.
        '''
        assert isinstance(otherImpl, Implies), "expected an Implies object"
        if self.conclusion == otherImpl.hypothesis:
            return Implies(self.hypothesis, otherImpl.conclusion)
        elif self.hypothesis == otherImpl.conclusion:
            return Implies(otherImpl.hypothesis, self.conclusion)
    
    def deriveHypotheticalContradiction(self):
        '''
        If this is an Implies expression with a FALSE conclusion, this will derive and return the Not(hypothesis)
        given isBool(hypothesis), or, if the hypothesis is a Not expression, Not(negHyp), then this will derive and
        return negHyp given isBool(negHyp).
        '''
        from basicLogic import A
        assert self.conclusion == FALSE
        if isinstance(self.hypothesis, Not):
            from basicLogic import hypotheticalContraNegation
            return hypotheticalContraNegation.specialize({A:self.hypothesis.operand}).deriveConclusion()
        else:
            from basicLogic import hypotheticalContradiction
            return hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion()
    
    def generalize(self, newForallVars, newConditions=None):
        '''
        This makes a generalization of this expression, prepending Forall 
        operations according to newForallVars and newConditions that will bind
        'arbitrary' free variables.  This overrides the Expression version
        to absorb hypothesis into conditions if they match.  For example, 
        [A(x) => [B(x, y) => P(x, y)]] generalized forall_{x, y | A(x), B(x, y)}
        becomes forall_{x | A(x)} forall_{y | B(x, y)} P(x, y),
        '''
        hypothesizedConditions = set()
        newConditionsSet = set(newConditions) if newConditions != None else set()
        expr = self
        while isinstance(expr, Implies) and expr.hypothesis in newConditionsSet:
            hypothesizedConditions.add(expr.hypothesis)
            expr = expr.conclusion
        if len(hypothesizedConditions) == 0:
            # Just use the Expression version
            return Expression.generalize(self, newForallVars, newConditions)
        return Forall(newForallVars, expr, newConditions)
        
    def applyTransposition(self):
        '''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will derive from self and return as follows.
        From Not(A) => Not(B), derive and return B => A.
        From Not(A) => B, derive Not(B) => A.
        From A => Not(B), derive B => Not(A).
        From A => B, derive Not(B) => Not(A).
        '''
        from basicLogic import A, B, transpositionFromNegated, transpositionFromNegatedHypothesis, transpositionFromNegatedConclusion, transpositionToNegated
        if isinstance(self.hypothesis, Not) and isinstance(self.conclusion, Not):
            return transpositionFromNegated.specialize({B:self.hypothesis.operand, A:self.conclusion.operand}).deriveConclusion()
        elif isinstance(self.hypothesis, Not):
            return transpositionFromNegatedHypothesis.specialize({B:self.hypothesis.operand, A:self.conclusion}).deriveConclusion()
        elif isinstance(self.conclusion, Not):
            return transpositionFromNegatedConclusion.specialize({B:self.hypothesis, A:self.conclusion.operand}).deriveConclusion()
        else:
            return transpositionToNegated.specialize({B:self.hypothesis, A:self.conclusion}).deriveConclusion()
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from basicLogic import impliesTT, impliesTF, impliesFT, impliesFF, evaluateBooleanBinaryOperation
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return impliesTT
            elif A == TRUE and B == FALSE: return impliesTF
            elif A == FALSE and B == TRUE: return impliesFT
            elif A == FALSE and B == FALSE: return impliesFF
        return evaluateBooleanBinaryOperation(self, baseEvalFn)    

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, [A])
        self.operand = A

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'not'
        elif formatType == MATHML:
            return '<mo>&#x00AC;</mo>'

    def formatted(self, formatType, fenced=False):
        if formatType == MATHML:
            outStr = ''
            if fenced: outStr += "<mfenced separators=''>"
            outStr += '<mrow>' + self.formattedOperator(formatType) + self.operand.formatted(formatType, fenced=True) + '</mrow>'
            if fenced: outStr += '</mfenced>'
            return outStr
        else:
            return Operation.formatted(self, formatType, fenced)        

    def remake(self, operator, operands):
        if operator == NOT and len(operands) == 1:
            return Not(operands[0])
        else:
            return Operation.remake(self, operator, operands)    
        
    def evaluate(self):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from basicLogic import A, notT, notF, substitute
        if self.operand == TRUE: return notT
        elif self.operand == FALSE: return notF
        operandEval = self.operand.evaluate()
        return substitute(operandEval, Not(A), A).evaluate()
    
    def equateNegatedToFalse(self):
        '''
        Derive and return [A = FALSE] from this Not(A) expression.
        Note, see Equals.deriveFromBooleanEquality for the reverse process.
        '''
        from basicLogic import A, notImpliesEqF
        return notImpliesEqF.specialize({A:self.operand}).deriveConclusion()
    
    def deriveFromDoubleNegation(self):
        '''
        Derive and return A given self and IsBool(A) where self is Not(Not(A)).
        Also see version in NotEquals.
        '''
        from basicLogic import A, fromDoubleNegation
        if isinstance(self.operand, Not):
            return fromDoubleNegation.specialize({A:self.operand.operand}).deriveConclusion() 
        
    def deriveContradiction(self):
        '''
        From Not(A) (self), derive and return A=>FALSE.
        '''
        from basicLogic import A, contradictionFromNegation
        return contradictionFromNegation.specialize({A:self.operand})
    
    def deriveNotEquals(self):
        '''
        Derive and return A != B given self where self is Not(A=B).
        '''
        from eqOps import Equals
        from basicLogic import A, B, foldNotEquals
        if isinstance(self.operand, Equals):
            return foldNotEquals.specialize({A:self.operand.lhs, B:self.operand.rhs}).deriveConclusion()
        
class And(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do And(A, B) to get AND{A}{B} or 
        And([A, B, C]) to get AND{A}{AND{B}{C}}, etc.
        '''
        AssociativeBinaryOperation.__init__(self, AND, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'and'
        elif formatType == MATHML:
            return '<mo>&#x2227;</mo>'

    def remake(self, operator, operands):
        if operator == AND and len(operands) == 2:
            return And(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
        
    def deriveLeft(self):
        '''
        Derive and return the first operand of this conjunctive, A given this [A and B].
        '''
        from basicLogic import A, B, andImpliesLeft
        return andImpliesLeft.specialize({A:self.operands[0], B: self.operands[1]}).deriveConclusion()

    def deriveRight(self):
        '''
        Derive and return the second operand of this conjunctive, B given this [A and B].
        '''
        from basicLogic import A, B, andImpliesRight
        return andImpliesRight.specialize({A:self.operands[0], B: self.operands[1]}).deriveConclusion()
        
    def decompose(self):
        '''
        Derive and return the both operands of this conjunctive, (A, B) given this [A and B].
        '''        
        return (self.deriveLeft(), self.deriveRight())
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from basicLogic import andTT, andTF, andFT, andFF, evaluateBooleanBinaryOperation
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return andTT
            elif A == TRUE and B == FALSE: return andTF
            elif A == FALSE and B == TRUE: return andFT
            elif A == FALSE and B == FALSE: return andFF
        return evaluateBooleanBinaryOperation(self, baseEvalFn)

class Or(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do Or(A, B) to get Or{A}{B} or 
        Or([A, B, C]) to get OR{A}{OR{B}{C}}, etc.
        '''
        AssociativeBinaryOperation.__init__(self, OR, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'or'
        elif formatType == MATHML:
            return '<mo>&#x2228;</mo>'

    def remake(self, operator, operands):
        if operator == OR and len(operands) == 2:
            return Or(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from basicLogic import orTT, orTF, orFT, orFF, evaluateBooleanBinaryOperation
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return orTT
            elif A == TRUE and B == FALSE: return orTF
            elif A == FALSE and B == TRUE: return orFT
            elif A == FALSE and B == FALSE: return orFF
        return evaluateBooleanBinaryOperation(self, baseEvalFn)

# if and only if: A => B and B => A
class Iff(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, IFF, A, B)
        self.A = A
        self.B = B
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '<=>'
        elif formatType == MATHML:
            return '<mo>&#x21D4;</mo>'

    def remake(self, operator, operands):
        if operator == IFF and len(operands) == 2:
            return Iff(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

    def deriveLeftImplication(self):
        from basicLogic import A, B, iffImpliesLeft
        return iffImpliesLeft.specialize({A: self.A, B: self.B}).deriveConclusion()
        
    def deriveLeft(self):
        return self.deriveLeftImplication().deriveConclusion()

    def deriveRightImplication(self):
        from basicLogic import A, B, iffImpliesRight
        return iffImpliesRight.specialize({A: self.A, B: self.B}).deriveConclusion()

    def deriveRight(self):
        return self.deriveRightImplication().deriveConclusion()
    
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from basicLogic import iffTT, iffTF, iffFT, iffFF, evaluateBooleanBinaryOperation
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return iffTT
            elif A == TRUE and B == FALSE: return iffTF
            elif A == FALSE and B == TRUE: return iffFT
            elif A == FALSE and B == FALSE: return iffFF
        return evaluateBooleanBinaryOperation(self, baseEvalFn)      
