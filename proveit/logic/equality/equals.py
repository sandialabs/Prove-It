from proveit import BinaryOperation, USE_DEFAULTS, ProofFailure
from proveit import Variable, Literal, Operation, Lambda
from proveit.common import A, P, X, f, x, y, z
from transitivity_search import transitivitySearch

pkg = __package__

EQUALS = Literal(pkg, '=')

class Equals(BinaryOperation):
    # map Expressions to sets of KnownTruths of equalities that involve the Expression
    # on the left hand or right hand side.
    knownEqualities = dict()
    
    def __init__(self, a, b):
        BinaryOperation.__init__(self, EQUALS, a, b)
        self.lhs = a
        self.rhs = b
        
    def deriveSideEffects(self, knownTruth):
        '''
        Record the knownTruth in Equals.knownEqualities, associated from
        the left hand side and the right hand side.  This information may
        be useful for concluding new equations via transitivity.  Also
        derive the reversed form, as a side effect.  If the right side
        is TRUE or FALSE, `deriveViaBooleanEquality` as a side effect.
        If this is a 1-step evaluation, an axiom or theorem whose
        left side is an Evaluatable (proveit._generic_.evaluatable) and 
        right side is an "irreducible value" 
        (see proveit._generic_.evaluatable.isIrreduciblValue), 
        store the KnownTruth in the Evaluatable.evaluations dictionary
        automatically (mapping the lhs to the knownTruth).
        '''
        from proveit.logic import TRUE, FALSE
        from proveit._generic_.evaluatable import Evaluatable, isIrreducibleValue
        Equals.knownEqualities.setdefault(self.lhs, set()).add(knownTruth)
        Equals.knownEqualities.setdefault(self.rhs, set()).add(knownTruth)
        if (self.lhs != self.rhs):
            # automatically derive the reversed form which is equivalent
            self.deriveReversed(knownTruth.assumptions)
        if self.rhs in (TRUE, FALSE):
            # automatically derive A from A=TRUE or Not(A) from A=FALSE
            self.deriveViaBooleanEquality(knownTruth.assumptions)
        if len(knownTruth.assumptions)==0 and isinstance(self.lhs, Evaluatable) and isIrreducibleValue(self.rhs):
            if knownTruth.proof().numSteps <= 1:
                Evaluatable.evaluations[self.lhs] = knownTruth
            
        
    def conclude(self, assumptions):
        '''
        Use other equalities that are known to be true to try to conclude 
        this equality via transitivity.  For example, if a=b, b=c, and c=d are 
        known truths (under the given assumptions), we can conclude that a=d
        (under these assumptions).  Also, reflexive equations (x=x) are
        concluded automatically, as are x=TRUE or TRUE=x given x
        and x=FALSE or FALSE=x given Not(x).
        '''
        from proveit.logic import TRUE, FALSE
        if self.lhs==self.rhs:
            return self.concludeViaReflexivity()
        if self.lhs or self.rhs in (TRUE, FALSE):
            try:
                return self.concludeBooleanEquality(assumptions)
            except ProofFailure:
                pass
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return transitivitySearch(self, assumptions)
                
    @staticmethod
    def knownRelationsFromLeft(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Equals involving the given expression on
        the left hand side, yield the KnownTruth and the right hand side.
        '''
        for knownTruth in Equals.knownEqualities.get(expr, frozenset()):
            if knownTruth.lhs == expr:
                if assumptionsSet.issuperset(knownTruth.assumptions):
                    yield (knownTruth, knownTruth.rhs)
    
    @staticmethod
    def knownRelationsFromRight(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Equals involving the given expression on
        the right hand side, yield the KnownTruth and the left hand side.
        '''
        for knownTruth in Equals.knownEqualities.get(expr, frozenset()):
            if knownTruth.rhs == expr:
                if assumptionsSet.issuperset(knownTruth.assumptions):
                    yield (knownTruth, knownTruth.lhs)
            
    @classmethod
    def operatorOfOperation(subClass):
        return EQUALS    

    def concludeViaReflexivity(self):
        '''
        Prove and return self of the form x = x.
        '''
        from axioms import equalsReflexivity
        assert self.lhs == self.rhs
        return equalsReflexivity.specialize({x:self.lhs})
            
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x = y derive y = x.  This derivation is an automatic side-effect.
        '''
        from axioms import equalsSymmetry
        return equalsSymmetry.specialize({x:self.lhs, y:self.rhs}, assumptions)
            
    def applyTransitivity(self, otherEquality, assumptions=USE_DEFAULTS):
        '''
        From x = y (self) and y = z (otherEquality) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        '''
        from theorems import equalsTransitivity
        # We can assume that y=x will be a KnownTruth if x=y is a KnownTruth because it is derived as a side-effect.
        if self.rhs == otherEquality.lhs:
            return equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}, assumptions)
        elif self.rhs == otherEquality.rhs:
            return equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.lhs}, assumptions)
        elif self.lhs == otherEquality.lhs:
            return equalsTransitivity.specialize({x:self.rhs, y:self.lhs, z:otherEquality.rhs}, assumptions)
        elif self.lhs == otherEquality.rhs:
            return equalsTransitivity.specialize({x:self.rhs, y:self.lhs, z:otherEquality.lhs}, assumptions)
        else:
            raise TransitivityException(self, otherEquality)
        
    def deriveViaBooleanEquality(self, assumptions=USE_DEFAULTS):
        '''
        From A = TRUE derive A, or from A = FALSE derive Not(A).  This derivation
        is an automatic side-effect.
        Note, see deriveStmtEqTrue or Not.equateNegatedToFalse for the reverse process.
        '''
        from proveit.logic import TRUE, FALSE        
        from proveit.logic.boolean.axioms import eqTrueElim
        from proveit.logic.boolean.negation.theorems import notFromEqFalse
        if self.rhs == TRUE:
            return eqTrueElim.specialize({A:self.lhs}, assumptions) # A
        elif self.rhs == FALSE:
            return notFromEqFalse.specialize({A:self.lhs}, assumptions) # Not(A)
        
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A=FALSE, derive A=>FALSE.
        '''
        from proveit.logic import FALSE        
        from theorems import contradictionFromFalseEquivalence, contradictionFromFalseEquivalenceReversed
        if self.rhs == FALSE:
            return contradictionFromFalseEquivalence.specialize({A:self.lhs}).deriveConclusion(assumptions)
        elif self.lhs == FALSE:
            return contradictionFromFalseEquivalenceReversed.specialize({A:self.rhs}).deriveConclusion(assumptions)
    
    def concludeBooleanEquality(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form (A=TRUE) assuming A, A=FALSE assuming Not(A), [Not(A)=FALSE] assuming A.
        '''
        from proveit.logic import TRUE, FALSE, Not        
        from proveit.logic.boolean.axioms import eqTrueIntro
        from proveit.logic.boolean.negation.theorems import eqFalseFromNegation
        if self.rhs == TRUE:
            return eqTrueIntro.specialize({A:self.lhs}, assumptions)
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                return eqFalseFromNegation.specialize({A:self.lhs.operands}, assumptions)
            else:
                return Not(self.lhs).equateNegatedToFalse(assumptions)
        elif self.lhs == TRUE or self.lhs == FALSE:
            return Equals(self.rhs, self.lhs).prove(assumptions).deriveReversed(assumptions)
        raise ProofFailure(self, assumptions, "May only conclude via boolean equality if one side of the equality is TRUE or FALSE")
    
    def deriveIsInSingleton(self, assumptions=USE_DEFAULTS):
        '''
        From (x = y), derive (x in {y}).
        '''
        from proveit.logic.set_theory.axioms import singletonDef
        return singletonDef.specialize({x:self.lhs, y:self.rhs}).deriveLeftViaEquivalence(assumptions)
    
    """
    def _subFn(self, fnExpr, fnArg, subbing, replacement):
        if fnArg is None:
            dummyVar = safeDummyVar(self, fnExpr)
            if isinstance(replacement, ExpressionList):
                fnArg = Etcetera(MultiVariable(dummyVar))
            elif isinstance(replacement, ExpressionTensor):
                fnArg = Block(dummyVar)
            else:
                fnArg = dummyVar
            fnExpr = fnExpr.substituted({subbing:fnArg})
            if dummyVar not in fnExpr.freeVars():
                raise Exception('Expression to be substituted is not found within the expression that the substitution is applied to.')
        return fnExpr, fnArg
    """
    
    @staticmethod
    def _lambdaExpr(lambdaMap):
        if hasattr(lambdaMap, 'lambdaMap'):
            lambdaExpr = lambdaMap.lambdaMap()
        else: lambdaExpr = lambdaMap
        if not isinstance(lambdaExpr, Lambda):
            raise TypeError('lambdaMap is expected to be a Lambda Expression or return a Lambda Expression via calling lambdaMap()')
        return lambdaExpr
    
    def substitution(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given f(x), derive f(x)=f(y).
        f(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular)
        '''
        from axioms import substitution
        fxLambda = Equals._lambdaExpr(lambdaMap)
        return substitution.specialize({x:self.lhs, y:self.rhs, f:fxLambda}, assumptions=assumptions)
        
    def lhsSubstitute(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(y), derive P(x) assuming P(y).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular).
        '''
        from theorems import substitute
        PxLambda = Equals._lambdaExpr(lambdaMap)
        return substitute.specialize({x:self.rhs, y:self.lhs, P:PxLambda}, assumptions=assumptions)
        
    def rhsSubstitute(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(x), derive P(y) assuming P(x).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular).
        '''
        from theorems import substitute
        PxLambda = Equals._lambdaExpr(lambdaMap)
        return substitute.specialize({x:self.lhs, y:self.rhs, P:PxLambda}, assumptions=assumptions)
        
    def deriveRightViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        return self.rhsSubstitute(Lambda(X, X), assumptions)

    def deriveLeftViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        return self.lhsSubstitute(Lambda(X, X), assumptions)
    
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this equality statement is in the set of Booleans.
        '''
        from axioms import equalityInBool
        return equalityInBool.specialize({x:self.lhs, y:self.rhs})
        
    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to TRUE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from proveit.logic import TRUE
        from proveit.logic.boolean.boolOps import _evaluate
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            if self.lhs == self.rhs:
                # simple case where both sides are the same, use reflexivity
                return Equals(self.concludeViaReflexivity(), TRUE).concludeBooleanEquality()
            
            # evaluate both sides and see if simplification is possible
            lhsSimpl = self.lhs
            rhsSimpl = self.rhs
            try:
                lhsEval = self.lhs.evaluate()
                lhsSimpl = lhsEval.rhs
            except AttributeError:
                lhsEval = None
            try:
                rhsEval = self.rhs.evaluate()
                rhsSimpl = rhsEval.rhs
            except AttributeError:
                rhsEval = None
    
            if lhsEval is None and rhsEval is None:
                # Cannot simplify further.  Use evalEquality.
                return lhsSimpl.evalEquality(rhsSimpl)
            else:         
                # evaluate the simplified version
                simplEval = Equals(lhsSimpl, rhsSimpl).evaluate()
                val = simplEval.rhs
                # Using substitution, go from simplEval to self=val
                if lhsEval is not None:
                    lhsEval.lhsSubstitute(Equals(Equals(X, rhsSimpl), val), X)
                if rhsEval is not None:
                    rhsEval.lhsSubstitute(Equals(Equals(self.lhs, X), val), X)
                return Equals(self, val)
            
        return _evaluate(self, doEval)
        
"""
This is obsolete (mostly) -- use proveit.lambda_map techniques instead.

def _autoSub(outcome, outerExpr, superExpr, subExpr, eqGenMethodName, eqGenMethodArgs=None, eqGenKeywordArgs=None, criteria=None, subExprClass=None, suppressWarnings=False):
    if eqGenMethodArgs is None: eqGenMethodArgs = []
    if eqGenKeywordArgs is None: eqGenKeywordArgs = dict()
    meetsCriteria = (subExprClass is None or isinstance(subExpr, subExprClass)) and \
        (criteria is None or criteria(subExpr))
    if meetsCriteria and hasattr(subExpr, eqGenMethodName):
        generatedEquality = None
        try:
            generatedEquality = getattr(subExpr, eqGenMethodName)(*eqGenMethodArgs, **eqGenKeywordArgs)
        except Exception as e:
            if not suppressWarnings:
                print "Warning, failure in autosub attempt when applying '" + eqGenMethodName + "' method to " + str(subExpr) + ":"
                print e
                print "Continuing on"
            
        if generatedEquality is not None and isinstance(generatedEquality, Equals) and (generatedEquality.lhs == subExpr or generatedEquality.rhs == subExpr):
            if superExpr == outerExpr:
                # substitute all occurences
                fnExpr, fnArgs = outerExpr, None 
            else:
                # substitute only occurences within superExpr
                subbing = generatedEquality.lhs if generatedEquality.lhs == subExpr else generatedEquality.rhs
                replacement = generatedEquality.rhs if generatedEquality.lhs == subExpr else generatedEquality.lhs
                fnExpr, fnArgs = generatedEquality._subFn(superExpr, None, subbing, replacement)
                fnExpr = outerExpr.substituted({superExpr:fnExpr})
            if outcome == 'substitution':
                return generatedEquality.substitution(fnExpr, fnArgs)
            elif generatedEquality.lhs == subExpr:
                if outcome == 'substitute':
                    return generatedEquality.rhsSubstitute(fnExpr, fnArgs)
                elif outcome == 'statement_substitution':
                    return generatedEquality.rhsStatementSubstitute(fnExpr, fnArgs)
            elif generatedEquality.rhs == subExpr:
                if outcome == 'substitute':
                    return generatedEquality.lhsSubstitute(fnExpr, fnArgs)
                elif outcome == 'statement_substitution':
                    return generatedEquality.lhsStatementSubstitute(fnExpr, fnArgs)
    for subExpr in subExpr.subExprGen():
        result = _autoSub(outcome, outerExpr, superExpr, subExpr, eqGenMethodName, eqGenMethodArgs, eqGenKeywordArgs, criteria, subExprClass, suppressWarnings)
        if result is not None: return result
    return None            
    
def autoSubstitute(expr, eqGenMethodName, eqGenMethodArgs=None, eqGenKeywordArgs=None, criteria=None, subExprClass=None, superExpr=None, suppressWarnings = False):
    '''
    From a given expr = P(x), derives and returns some P(y) via some x=y that is generated by
    calling a method of the name eqGenMethodName on one of its sub-expressions.  eqGenMethodArgs
    and eqGenKeywordArgs may be a list of arguments and/or a dictionary of keyword arguments
    respectively to pass on to the eqGenMethodName method.  If provided, criteria, subExprClass,
    and superExpr will force selectivity in choosing the sub-expression to generate x=y.
    Specificially the sub-expression must be a sub-expression of superExpr (if provided)
    beyond being a sub-expression of expr, it must be an instance of subExprClass (if provided), 
    and the criteria method (if provide) must return true when passed in the sub-expression.
    If superExpr is provided, replacements are only made within superExpr.
    '''
    if superExpr is None: superExpr = expr
    return _autoSub('substitute', expr, superExpr, superExpr, eqGenMethodName, eqGenMethodArgs, eqGenKeywordArgs, criteria, subExprClass, suppressWarnings)

def autoSubstitution(expr, eqGenMethodName, eqGenMethodArgs=None, eqGenKeywordArgs=None, criteria=None, subExprClass=None, superExpr=None, suppressWarnings = False):
    '''
    From a given expr = f(x), derives and returns some f(x) = f(y) via some x=y that is generated by
    calling a method of the name eqGenMethodName on one of its sub-expressions.  eqGenMethodArgs
    and eqGenKeywordArgs may be a list of arguments and/or a dictionary of keyword arguments
    respectively to pass on to the eqGenMethodName method.  If provided, criteria, subExprClass,
    and superExpr will force selectivity in choosing the sub-expression to generate x=y.
    Specificially the sub-expression must be a sub-expression of superExpr (if provided)
    beyond being a sub-expression of expr, it must be an instance of subExprClass (if provided), 
    and the criteria method (if provide) must return true when passed in the sub-expression.
    If superExpr is provided, replacements are only made within superExpr.
    '''
    if superExpr is None: superExpr = expr
    return _autoSub('substitution', expr, superExpr, superExpr, eqGenMethodName, eqGenMethodArgs, eqGenKeywordArgs, criteria, subExprClass, suppressWarnings)

def autoStatementSubstitution(expr, eqGenMethodName, eqGenMethodArgs=None, eqGenKeywordArgs=None, criteria=None, subExprClass=None, superExpr=None, suppressWarnings = False):
    '''
    From a given expr = P(x), derives and returns some P(x) => P(y) via some x=y that is 
    generated by calling a method of the name eqGenMethodName on one of its sub-expressions.
    eqGenMethodArgs and eqGenKeywordArgs may be a list of arguments and/or a dictionary of 
    keyword arguments respectively to pass on to the eqGenMethodName method.  If provided, 
    criteria, subExprClass, and superExpr will force selectivity in choosing the sub-expression 
    to generate x=y.  Specificially the sub-expression must be a sub-expression of superExpr 
    (if provided) beyond being a sub-expression of expr, it must be an instance of subExprClass 
    (if provided), and the criteria method (if provide) must return true when passed in the 
    sub-expression. If superExpr is provided, replacements are only made within superExpr.
    '''
    if superExpr is None: superExpr = expr
    return _autoSub('statement_substitution', expr, superExpr, superExpr, eqGenMethodName, eqGenMethodArgs, eqGenKeywordArgs, criteria, subExprClass, suppressWarnings)        
"""

"""
Either move this elsewhere or use other techniques.  Perhaps no longer needed.

def generateSubExpressions(expr, criteria=None, subExprClass=None):
    meetsCriteria = (subExprClass is None or isinstance(expr, subExprClass)) and \
        (criteria is None or criteria(expr))
    if meetsCriteria: yield expr
    for subExpr in expr.subExprGen():
        for subSubExpr in generateSubExpressions(subExpr, criteria, subExprClass):
            yield subSubExpr

def extractSubExpr(expr, criteria=None, subExprClass=None):
    for subExpr in generateSubExpressions(expr, criteria=criteria, subExprClass=subExprClass):
        return subExpr
    print "Sub expression meeting the criteria not found"

"""

class TransitivityException:
    def __init__(self, expr1, expr2):
        self.expr1 = expr1
        self.expr2 = expr2
    
    def __str__(self):
        return 'Transitivity cannot be applied unless there is something in common in the equalities'