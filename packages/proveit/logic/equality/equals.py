from proveit import asExpression, defaults, USE_DEFAULTS, ProofFailure
from proveit import Literal, Operation, Lambda
from proveit import TransitiveRelation
from proveit.logic.irreducible_value import IrreducibleValue, isIrreducibleValue
from proveit._common_ import A, P, Q, f, x, y, z

class Equals(TransitiveRelation):
    # operator of the Equals operation
    _operator_ = Literal(stringFormat='=', context=__file__)        
    
    # map Expressions to sets of KnownTruths of equalities that involve the Expression
    # on the left hand or right hand side.
    knownEqualities = dict()

    # Subset of knownEqualities that have irreducible values on the right
    # hand side.
    evaluations = dict()
    
    # Record found inversions.  See the invert method.
    # Maps (lambda_map, rhs) pairs to a list of
    # (known_equality, inversion) pairs, recording previous results
    # of the invert method for future reference.
    inversions = dict()
        
    def __init__(self, a, b):
        TransitiveRelation.__init__(self, Equals._operator_, a, b)
        
    def sideEffects(self, knownTruth):
        '''
        Record the knownTruth in Equals.knownEqualities, associated from
        the left hand side and the right hand side.  This information may
        be useful for concluding new equations via transitivity. 
        If the right hand side is an "irreducible value" (see 
        isIrreducibleValue), also record it in Equals.evaluations for use
        when the evaluate method is called.   Some side-effects
        derivations are also attempted depending upon the form of
        this equality.
        '''
        from proveit.logic.boolean._common_ import TRUE, FALSE
        Equals.knownEqualities.setdefault(self.lhs, set()).add(knownTruth)
        Equals.knownEqualities.setdefault(self.rhs, set()).add(knownTruth)
        if isIrreducibleValue(self.rhs):
            Equals.evaluations.setdefault(self.lhs, set()).add(knownTruth)
        if (self.lhs != self.rhs):
            # automatically derive the reversed form which is equivalent
            yield self.deriveReversed
        if self.rhs == FALSE:
            # derive lhs => FALSE from lhs = FALSE
            yield self.deriveContradiction
            # derive lhs from Not(lhs) = FALSE, if self is in this form
            yield self.deriveViaFalsifiedNegation
        if self.rhs in (TRUE, FALSE):
            # automatically derive A from A=TRUE or Not(A) from A=FALSE
            yield self.deriveViaBooleanEquality
        
    def negationSideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for a negated equation.        
        '''
        from proveit.logic.boolean._common_ import FALSE
        yield self.deduceNotEquals # A != B from not(A=B)
        if self.rhs == FALSE:
            yield self.deduceViaNegatedFalsification # A from not(A=FALSE) and A in Booleans
                
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
        try:
            # try to prove the equality via evaluation reduction.
            # if that is possible, it is a relatively straightforward thing to do.
            return BinaryOperation.conclude(assumptions)
        except:
            pass
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return TransitiveRelation.conclude(self, assumptions)
                
    @staticmethod
    def knownRelationsFromLeft(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Equals involving the given expression on
        the left hand side, yield the KnownTruth and the right hand side.
        '''
        for knownTruth in Equals.knownEqualities.get(expr, frozenset()):
            if knownTruth.lhs == expr:
                if knownTruth.isSufficient(assumptionsSet):
                    yield (knownTruth, knownTruth.rhs)
    
    @staticmethod
    def knownRelationsFromRight(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Equals involving the given expression on
        the right hand side, yield the KnownTruth and the left hand side.
        '''
        for knownTruth in Equals.knownEqualities.get(expr, frozenset()):
            if knownTruth.rhs == expr:
                if knownTruth.isSufficient(assumptionsSet):
                    yield (knownTruth, knownTruth.lhs)
            
    def concludeViaReflexivity(self):
        '''
        Prove and return self of the form x = x.
        '''
        from _axioms_ import equalsReflexivity
        assert self.lhs == self.rhs
        return equalsReflexivity.specialize({x:self.lhs})
            
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x = y derive y = x.  This derivation is an automatic side-effect.
        '''
        from _theorems_ import equalsReversal
        return equalsReversal.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)

    def deduceNotEquals(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x != y assuming not(x = y), where self is x=y.
        '''
        from not_equals import NotEquals
        return NotEquals(self.lhs, self.rhs).concludeAsFolded(assumptions)
                        
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From x = y (self) and y = z (other) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        If "other" is not an equality, reverse roles and call 'applyTransitivity'
        from the "other" side.
        '''
        from _axioms_ import equalsTransitivity
        other = asExpression(other)
        if not isinstance(other, Equals):
            # If the other relation is not "Equals", call from the "other" side.
            return other.applyTransitivity(self, assumptions)
        otherEquality = other
        # We can assume that y=x will be a KnownTruth if x=y is a KnownTruth because it is derived as a side-effect.
        if self.rhs == otherEquality.lhs:
            return equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}, assumptions=assumptions)
        elif self.rhs == otherEquality.rhs:
            return equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.lhs}, assumptions=assumptions)
        elif self.lhs == otherEquality.lhs:
            return equalsTransitivity.specialize({x:self.rhs, y:self.lhs, z:otherEquality.rhs}, assumptions=assumptions)
        elif self.lhs == otherEquality.rhs:
            return equalsTransitivity.specialize({x:self.rhs, y:self.lhs, z:otherEquality.lhs}, assumptions=assumptions)
        else:
            raise TransitivityException(self, otherEquality)
        
    def deriveViaBooleanEquality(self, assumptions=USE_DEFAULTS):
        '''
        From A = TRUE derive A, or from A = FALSE derive Not(A).  This derivation
        is an automatic side-effect.
        Note, see deriveStmtEqTrue or Not.equateNegatedToFalse for the reverse process.
        '''
        from proveit.logic import TRUE, FALSE        
        from proveit.logic.boolean._axioms_ import eqTrueElim
        from proveit.logic import Not
        if self.rhs == TRUE:
            return eqTrueElim.specialize({A:self.lhs}, assumptions=assumptions) # A
        elif self.rhs == FALSE:
            return Not(self.lhs).prove(assumptions=assumptions) # Not(A)
        
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A=FALSE, and assuming A, derive FALSE.
        '''
        from proveit.logic import FALSE        
        from _theorems_ import contradictionViaFalsification
        if self.rhs == FALSE:
            return contradictionViaFalsification.specialize({A:self.lhs}, assumptions=assumptions)
        raise ValueError('Equals.deriveContradiction is only applicable if the right-hand-side is FALSE')
    
    def affirmViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A=FALSE), derive the conclusion provided that the negated conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import affirmViaContradiction
        return affirmViaContradiction(self, conclusion, assumptions)

    def denyViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A=FALSE), derive the negated conclusion provided that the conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import denyViaContradiction
        return denyViaContradiction(self, conclusion, assumptions)
            
    def deriveViaFalsifiedNegation(self, assumptions=USE_DEFAULTS):
        '''
        From Not(A)=FALSE, derive A.
        '''
        from proveit.logic.boolean import Not, FALSE
        from proveit.logic.boolean.negation._axioms_ import falsifiedNegationElim
        if isinstance(self.lhs, Not) and self.rhs == FALSE:
            return falsifiedNegationElim.specialize({A:self.lhs.operand}, assumptions=assumptions)
        raise ValueError('Equals.deriveViaContradiction is only applicable if the left-hand-side is a Not operation and the right-hand-side is FALSE')
    
    def deduceViaNegatedFalsification(self, assumptions=USE_DEFAULTS):
        '''
        From Not(A=FALSE) and assuming A in Booleans derive A, where self is A=FALSE.
        '''
        from proveit.logic.boolean import FALSE
        from proveit.logic.boolean.negation._theorems_ import fromNegatedFalsification
        if self.rhs == FALSE:
            return fromNegatedFalsification.specialize({A:self.lhs}, assumptions=assumptions)
        raise ValueError('Equals.deduceViaNegatedFalsification is only applicable if the right-hand-side is FALSE')
        
    
    def concludeBooleanEquality(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form (A=TRUE) assuming A, A=FALSE assuming Not(A), [Not(A)=FALSE] assuming A.
        '''
        from proveit.logic import TRUE, FALSE, Not        
        from proveit.logic.boolean._axioms_ import eqTrueIntro
        if self.rhs == TRUE:
            return eqTrueIntro.specialize({A:self.lhs}, assumptions=assumptions)
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                return self.lhs.evaluate(assumptions=assumptions)
            else:
                return Not(self.lhs).equateNegatedToFalse(assumptions)
        elif self.lhs == TRUE or self.lhs == FALSE:
            return Equals(self.rhs, self.lhs).prove(assumptions).deriveReversed(assumptions)
        raise ProofFailure(self, assumptions, "May only conclude via boolean equality if one side of the equality is TRUE or FALSE")
    
    def deriveIsInSingleton(self, assumptions=USE_DEFAULTS):
        '''
        From (x = y), derive (x in {y}).
        '''
        from proveit.logic.set_theory.enumeration._theorems_ import foldSingleton
        return foldSingleton.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
    
    @staticmethod
    def _lambdaExpr(lambdaMap, defaultGlobalReplSubExpr):
        from proveit.lambda_map import globalRepl
        if hasattr(lambdaMap, 'lambdaMap'):
            expr = lambdaMap.lambdaMap()
        else: expr = lambdaMap
        if not isinstance(expr, Lambda):
            # as a default, do a global replacement
            return globalRepl(expr, defaultGlobalReplSubExpr)
        return expr
    
    def substitution(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given f(x), derive f(x)=f(y).
        f(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from _axioms_ import substitution
        fxLambda = Equals._lambdaExpr(lambdaMap, self.lhs)
        return substitution.specialize({x:self.lhs, y:self.rhs, f:fxLambda}, assumptions=assumptions)
        
    def lhsSubstitute(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(y), derive P(x) assuming P(y).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        from _theorems_ import lhsSubstitute
        from _theorems_ import substituteTruth, substituteInTrue, substituteFalsehood, substituteInFalse
        from proveit.logic import TRUE, FALSE
        Plambda = Equals._lambdaExpr(lambdaMap, self.rhs)
        try:
            # try some alternative proofs that may be shorter, if they are usable
            if self.rhs == TRUE: # substituteTruth may provide a shorter proof options
                substituteTruth.specialize({x:self.lhs, P:Plambda}, assumptions=assumptions)
            elif self.lhs == TRUE: # substituteInTrue may provide a shorter proof options
                substituteInTrue.specialize({x:self.rhs, P:Plambda}, assumptions=assumptions)            
            elif self.rhs == FALSE: # substituteFalsehood may provide a shorter proof options
                substituteFalsehood.specialize({x:self.lhs, P:Plambda}, assumptions=assumptions)            
            elif self.lhs == FALSE: # substituteInFalse may provide a shorter proof options
                substituteInFalse.specialize({x:self.rhs, P:Plambda}, assumptions=assumptions)           
        except:
            pass 
        return lhsSubstitute.specialize({x:self.lhs, y:self.rhs, P:Plambda}, assumptions=assumptions)
        
    def rhsSubstitute(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(x), derive P(y) assuming P(x).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from _theorems_ import rhsSubstitute
        from _theorems_ import substituteTruth, substituteInTrue, substituteFalsehood, substituteInFalse
        from proveit.logic import TRUE, FALSE
        Plambda = Equals._lambdaExpr(lambdaMap, self.lhs)
        try:
            # try some alternative proofs that may be shorter, if they are usable
            if self.lhs == TRUE: # substituteTruth may provide a shorter proof options
                substituteTruth.specialize({x:self.rhs, P:Plambda}, assumptions=assumptions)
            elif self.rhs == TRUE: # substituteInTrue may provide a shorter proof options
                substituteInTrue.specialize({x:self.lhs, P:Plambda}, assumptions=assumptions)            
            elif self.lhs == FALSE: # substituteFalsehood may provide a shorter proof options
                substituteFalsehood.specialize({x:self.rhs, P:Plambda}, assumptions=assumptions)            
            elif self.rhs == FALSE: # substituteInFalse may provide a shorter proof options
                substituteInFalse.specialize({x:self.lhs, P:Plambda}, assumptions=assumptions)            
        except:
            pass
        return rhsSubstitute.specialize({x:self.lhs, y:self.rhs, P:Plambda}, assumptions=assumptions)
        
    def deriveRightViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        from _theorems_ import rhsViaEquivalence
        return rhsViaEquivalence.specialize({P:self.lhs, Q:self.rhs}, assumptions=assumptions)

    def deriveLeftViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        from _theorems_ import lhsViaEquivalence
        return lhsViaEquivalence.specialize({P:self.lhs, Q:self.rhs}, assumptions=assumptions)
    
    def otherSide(self, expr):
        '''
        Returns the 'other' side of the of the equation if the given expr is on one side.
        '''
        if expr == self.lhs:
            return self.rhs
        elif expr == self.rhs:
            return self.lhs
        raise ValueError('The given expression is expected to be one of the sides of the equation')
        
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this equality statement is in the set of Booleans.
        '''
        from _axioms_ import equalityInBool
        return equalityInBool.specialize({x:self.lhs, y:self.rhs})
        
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that may be evaluated to irreducible values that
        may be compared, or if there is a known evaluation of this
        equality, derive and return this expression equated to
        TRUE or FALSE.
        '''
        if self.lhs == self.rhs:
            # prove equality is true by reflexivity
            return evaluateTruth(self.prove().expr, assumptions=[])
        if isIrreducibleValue(self.lhs) and isIrreducibleValue(self.rhs):
            # Irreducible values must know how to evaluate the equality
            # between each other, where appropriate.
            return self.lhs.evalEquality(self.rhs)
        return BinaryOperation.evaluate(self, assumptions)
    
    def invert(self, lambda_map, rhs, assumptions=USE_DEFAULTS):
        '''
        Given some x -> f(x) map and a right-hand-side, find the
        x for which f(x) = rhs amongst known equalities under the
        given assumptions.  Return this x if one is found; return
        None otherwise.
        '''
        if (lambda_map, rhs) in Equals.inversions:
            # Previous solution(s) exist.  Use one if the assumptions are sufficient.
            assumptionsSet = set(defaults.checkedAssumptions(assumptions)) 
            for known_equality, inversion in Equals.inversions[(lambda_map, rhs)]:
                if known_equality.isSufficient(assumptionsSet):
                    return inversion
            # Found previous solution
            return Equals.inversions[(lambda_map, rhs)]
        # Search among known relations for a solution.
        for known_equality in Equals.knownRelationsFromRight(rhs, assumptions):
            x = lambda_map.extractParameter(known_equality.lhs)
            if x is not None:
                # Found an inversion.  Store it for future reference.
                Equals.inversions.setdefault((lambda_map, rhs), []).append(known_equality, x)
                return x # Return the found inversion.
        return None # No inversion found.
    
def reduceOperands(operation, assumptions=USE_DEFAULTS):
    '''
    Attempt to return a provably equivalent expression whose operands
    are all irreducible values (IrreducibleValue objects).
    '''
    # Any of the operands that are not irreducible values must be replaced with their evaluation
    expr = operation
    while True:
        allReduced = True
        for operand in expr.operands:
            if not isIrreducibleValue(operand):
                # the operand is not an irreducible value so it must be evaluated
                operandEval = operand.evaluate(assumptions=assumptions)
                if not isIrreducibleValue(operandEval.rhs):
                    raise EvaluationError('Evaluations expected to be irreducible values')
                # substitute in the evaluated value
                expr = operandEval.substitution(expr).rhs
                allReduced = False
                break # start over (there may have been multiple substitutions)
        if allReduced: return expr

"""
def concludeViaReduction(expr, assumptions):
    '''
    Attempts to prove that the given expression is TRUE under the
    given assumptions via evaluating that the expression is equal to true.
    Returns the resulting KnownTruth if successful.
    '''
    from proveit.lambda_map import SubExprRepl
    if not isinstance(expr, Operation):
        # Can only really do reduction on an Operation.  But we can
        # try to do a proof by evaluation.
        expr.evaluate(assumptions)
        return expr.prove(assumptions)
    # reduce the operands
    reducedExpr = reduceOperands(expr, assumptions)
    # prove the reduced version
    knownTruth = reducedExpr.prove(assumptions)
    # now rebuild the original via lhsSubstitute (for a shorter proof than substitutions)
    for k, operand in enumerate(expr.operands):
        # for each operand, replace it with the original
        subExprRepl = SubExprRepl(knownTruth).operands[k]
        knownTruth = operand.evaluate(assumptions=assumptions).lhsSubstitute(subExprRepl, assumptions)
    assert knownTruth.expr == expr, 'Equivalence substitutions did not work out as they should have'
    return knownTruth
"""
            
def defaultEvaluate(expr, assumptions=USE_DEFAULTS, automation=True):
    '''
    Default attempt to evaluate the given expression under the given assumptions.
    If successful, returns a KnownTruth (using a subset of the given assumptions)
    that expresses an equality between the expression (on the left) and
    and irreducible value (see isIrreducibleValue).  Specifically, this
    method checks to see if an appropriate evaluation has already been
    proven.  If not, but if it is an Operation, call the evaluate method on
    all operands, make these substitions, then call evaluate on the expression
    with operands substituted for irreducible values.  It also treats, as a
    special case, evaluating the expression to be true if it is in the set
    of assumptions [also see KnownTruth.evaluate and evaluateTruth].
    '''
    from proveit.logic import TRUE, FALSE
    if isinstance(expr, IrreducibleValue):
        IrreducibleValue.evaluate(expr)
    assumptionsSet = set(defaults.checkedAssumptions(assumptions))
    # see if the expression is already known to be true as a special case
    try:
        expr.prove(assumptionsSet, automation=False)
        return evaluateTruth(expr, assumptionsSet) # A=TRUE given A
    except:
        pass
    # see if the negation of the expression is already known to be true as a special case
    try:
        expr.disprove(assumptionsSet, automation=False)
        return evaluateFalsehood(expr, assumptionsSet) # A=FALSE given Not(A)
    except:
        pass    # See if the expression already has a proven evaluation
    if expr in Equals.evaluations:
        candidates = []
        for knownTruth in Equals.evaluations[expr]:
            if knownTruth.isSufficient(assumptionsSet):
                candidates.append(knownTruth) # found existing evaluation suitable for the assumptions
        if len(candidates) >= 1:
            # return the "best" candidate with respect to fewest number of steps
            return min(candidates, key=lambda knownTruth: knownTruth.proof().numSteps)
    if not automation:
        raise EvaluationError('Unknown evaluation (without automation): ' + str(expr))
    # See if the expression is equal to something that has an evaluation or is 
    # already known to be true.
    if expr in Equals.knownEqualities:
        for knownTruth in Equals.knownEqualities[expr]:
            try:
                if knownTruth.isSufficient(assumptionsSet):
                    equivEval = defaultEvaluate(knownTruth.otherSide(expr), assumptions, automation=False)
                    return Equals(expr, equivEval.rhs).prove(assumptions=assumptions) # via transitivity
            except EvaluationError:
                pass     
    # try to evaluate via reduction
    if not isinstance(expr, Operation):
        raise EvaluationError('Unknown evaluation: ' + str(expr))
    reducedExpr = reduceOperands(expr, assumptions)
    if reducedExpr == expr:
        raise EvaluationError('Unable to evaluate: ' + str(expr))
    value = reducedExpr.evaluate().rhs
    if value == TRUE:
        # Attempt to evaluate via proving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluateTruth(expr, assumptions)
        except:
            pass
    if value == FALSE:
        # Attempt to evaluate via disproving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluateFalsehood(expr, assumptions)
        except:
            pass
    evaluation = Equals(expr, value).prove(assumptions=assumptions)
    # store it in the evaluations dictionary for next time
    Equals.evaluations.setdefault(expr, set()).add(evaluation)
    return evaluation  

def evaluateTruth(expr, assumptions):
    '''
    Attempts to prove that the given expression equals TRUE under
    the given assumptions via proving the expression.
    Returns the resulting KnownTruth evaluation if successful.
    '''
    from proveit.logic import TRUE
    return Equals(expr, TRUE).prove(assumptions)

def evaluateFalsehood(expr, assumptions):
    '''
    Attempts to prove that the given expression equals FALSE under
    the given assumptions via disproving the expression.
    Returns the resulting KnownTruth evaluationn if successful.
    '''
    from proveit.logic import FALSE
    return Equals(expr, FALSE).prove(assumptions)

class EvaluationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class TransitivityException:
    def __init__(self, expr1, expr2):
        self.expr1 = expr1
        self.expr2 = expr2
    
    def __str__(self):
        return 'Transitivity cannot be applied unless there is something in common in the equalities'