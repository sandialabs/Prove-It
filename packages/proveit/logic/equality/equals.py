from proveit import asExpression, defaults, USE_DEFAULTS, ProofFailure
from proveit import Literal, Operation, Lambda, ParameterExtractionError
from proveit import TransitiveRelation
from proveit.logic.irreducible_value import IrreducibleValue, isIrreducibleValue
from proveit._common_ import A, B, P, Q, f, x, y, z

class Equals(TransitiveRelation):
    # operator of the Equals operation
    _operator_ = Literal(stringFormat='=', context=__file__)        
    
    # map Expressions to sets of KnownTruths of equalities that involve the Expression
    # on the left hand or right hand side.
    knownEqualities = dict()
    
    # Map Expressions to a subset of knownEqualities that are 
    # deemed to effect simplifications of the inner expression
    # on te right hand side according to some canonical method 
    # of simplication determined by each operation.
    simplifications = dict()

    # Specific simplifications that simplify the inner expression to 
    # IrreducibleValue objects.
    evaluations = dict()
        
    # Record found inversions.  See the invert method.
    # Maps (lambda_map, rhs) pairs to a list of
    # (known_equality, inversion) pairs, recording previous results
    # of the invert method for future reference.
    inversions = dict()
    
    # Record the Equals objects being initialized (to avoid infinite
    # recursion while automatically deducing an equality is in Booleans).
    initializing = set()
    
    def __init__(self, a, b):
        TransitiveRelation.__init__(self, Equals._operator_, a, b)
        if self not in Equals.initializing:
            Equals.initializing.add(self)
            try:
                self.deduceInBool() # proactively prove (a=b) in Booleans.
            except:
                # may fail before the relevent _axioms_ have been generated
                pass # and that's okay            
            Equals.initializing.remove(self)
    
    def sideEffects(self, knownTruth):
        '''
        Record the knownTruth in Equals.knownEqualities, associated from
        the left hand side and the right hand side.  This information may
        be useful for concluding new equations via transitivity. 
        If the right hand side is an "irreducible value" (see 
        isIrreducibleValue), also record it in Equals.evaluations for use
        when the evaluation method is called.   Some side-effects
        derivations are also attempted depending upon the form of
        this equality.
        '''
        from proveit.logic.boolean._common_ import TRUE, FALSE
        Equals.knownEqualities.setdefault(self.lhs, set()).add(knownTruth)
        Equals.knownEqualities.setdefault(self.rhs, set()).add(knownTruth)
        if isIrreducibleValue(self.rhs):
            Equals.simplifications.setdefault(self.lhs, set()).add(knownTruth)
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
        if hasattr(self.lhs, 'equalitySideEffects'):
            for sideEffect in self.lhs.equalitySideEffects(knownTruth):
                yield sideEffect
        
    def negationSideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for a negated equation.        
        '''
        from proveit.logic.boolean._common_ import FALSE
        yield self.deduceNotEquals # A != B from not(A=B)
                
    def conclude(self, assumptions):
        '''
        Attempt to conclude the equality various ways:
        simple reflexivity (x=x), via an evaluation (if one side is an irreducible),
        or via transitivity.
        '''
        from proveit.logic import TRUE, FALSE, Implies, Iff
        if self.lhs==self.rhs:
            # Trivial x=x
            return self.concludeViaReflexivity()
        if self.lhs or self.rhs in (TRUE, FALSE):
            try:
                # Try to conclude as TRUE or FALSE.
                return self.concludeBooleanEquality(assumptions)
            except ProofFailure:
                pass
        if isIrreducibleValue(self.rhs):
            return self.lhs.evaluation()
        elif isIrreducibleValue(self.lhs):
            return self.rhs.evaluation().deriveReversed()
        try:
            Implies(self.lhs, self.rhs).prove(assumptions, automation=False)
            Implies(self.rhs, self.lhs).prove(assumptions, automation=False)
            # lhs => rhs and rhs => lhs, so attempt to prove lhs = rhs via lhs <=> rhs
            # which works when they can both be proven to be Booleans.
            try:
                return Iff(self.lhs, self.rhs).deriveEquality(assumptions)
            except:
                from proveit.logic.boolean.implication._theorems_ import eqFromMutualImpl
                return eqFromMutualImpl.specialize({A:self.lhs, B:self.rhs}, assumptions=assumptions)
        except ProofFailure:
            pass
        
        """
        # Use concludeEquality if available
        if hasattr(self.lhs, 'concludeEquality'):
            return self.lhs.concludeEquality(assumptions)
        if hasattr(self.rhs, 'concludeEquality'):
            return self.rhs.concludeEquality(assumptions)
        """
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
            
    def concludeViaReflexivity(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x = x.
        '''
        from ._axioms_ import equalsReflexivity
        assert self.lhs == self.rhs
        return equalsReflexivity.specialize({x:self.lhs})
                
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x = y derive y = x.  This derivation is an automatic side-effect.
        '''
        from ._theorems_ import equalsReversal
        return equalsReversal.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)

    def deduceNotEquals(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x != y assuming not(x = y), where self is x=y.
        '''
        from .not_equals import NotEquals
        return NotEquals(self.lhs, self.rhs).concludeAsFolded(assumptions)
                        
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From x = y (self) and y = z (other) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        If "other" is not an equality, reverse roles and call 'applyTransitivity'
        from the "other" side.
        '''
        from ._axioms_ import equalsTransitivity
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
            return Not(self.lhs).concludeViaFalsifiedNegation(assumptions=assumptions) # Not(A)
        
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A=FALSE, and assuming A, derive FALSE.
        '''
        from proveit.logic import FALSE        
        from ._theorems_ import contradictionViaFalsification
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
                return self.lhs.evaluation(assumptions=assumptions)
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
        from proveit._core_.expression.inner_expr import InnerExpr
        if isinstance(lambdaMap, InnerExpr):
            expr = lambdaMap.replMap()
        else: expr = lambdaMap
        if not isinstance(expr, Lambda):
            # as a default, do a global replacement
            return Lambda.globalRepl(expr, defaultGlobalReplSubExpr)
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
        from ._axioms_ import substitution
        fxLambda = Equals._lambdaExpr(lambdaMap, self.lhs)
        return substitution.specialize({x:self.lhs, y:self.rhs, f:fxLambda}, assumptions=assumptions)
        
    def subLeftSideInto(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(y), derive P(x) assuming P(y).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        from ._theorems_ import subLeftSideInto
        from ._theorems_ import substituteTruth, substituteInTrue, substituteFalsehood, substituteInFalse
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
        return subLeftSideInto.specialize({x:self.lhs, y:self.rhs, P:Plambda}, assumptions=assumptions)
        
    def subRightSideInto(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(x), derive P(y) assuming P(x).  
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from ._theorems_ import subRightSideInto
        from ._theorems_ import substituteTruth, substituteInTrue, substituteFalsehood, substituteInFalse
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
        return subRightSideInto.specialize({x:self.lhs, y:self.rhs, P:Plambda}, assumptions=assumptions)
        
    def deriveRightViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        from ._theorems_ import rhsViaEquivalence
        return rhsViaEquivalence.specialize({P:self.lhs, Q:self.rhs}, assumptions=assumptions)

    def deriveLeftViaEquivalence(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        from ._theorems_ import lhsViaEquivalence
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
        from ._axioms_ import equalityInBool
        return equalityInBool.specialize({x:self.lhs, y:self.rhs})
        
    def evaluation(self, assumptions=USE_DEFAULTS):
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
        return TransitiveRelation.evaluation(self, assumptions)
    
    @staticmethod
    def invert(lambda_map, rhs, assumptions=USE_DEFAULTS):
        '''
        Given some x -> f(x) map and a right-hand-side, find the
        x for which f(x) = rhs amongst known equalities under the
        given assumptions.  Return this x if one is found; return
        None otherwise.
        '''
        assumptionsSet = set(defaults.checkedAssumptions(assumptions)) 
        if (lambda_map, rhs) in Equals.inversions:
            # Previous solution(s) exist.  Use one if the assumptions are sufficient.
            for known_equality, inversion in Equals.inversions[(lambda_map, rhs)]:
                if known_equality.isSufficient(assumptionsSet):
                    return inversion
        # The mapping may be a trivial identity: f(x) = f(x)
        try:
            x = lambda_map.extractParameter(rhs)
            # Found a trivial inversion.  Store it for future reference.
            known_equality = Equals(rhs, rhs).prove()
            Equals.inversions.setdefault((lambda_map, rhs), []).append((known_equality, x))
            return x # Return the found inversion.
        except ParameterExtractionError:
            pass # well, it was worth a try
        # Search among known relations for a solution.
        for known_equality, lhs in Equals.knownRelationsFromRight(rhs, assumptionsSet):
            try:
                x = lambda_map.extractParameter(lhs)
                # Found an inversion.  Store it for future reference.
                Equals.inversions.setdefault((lambda_map, rhs), []).append((known_equality, x))
                return x # Return the found inversion.
            except ParameterExtractionError:
                pass # not a match.  keep looking.
        raise InversionError("No inversion found to map %s onto %s"%(str(lambda_map), str(rhs)))
    
def reduceOperands(innerExpr, inPlace=True, mustEvaluate=False, assumptions=USE_DEFAULTS):
    '''
    Attempt to return an InnerExpr object that is provably equivalent to
    the given innerExpr but with simplified operands at the inner-expression
    level. 
    If inPlace is True, the top-level expression must be a KnownTruth
    and the simplified KnownTruth is derived instead of an equivalence
    relation.
    If mustEvaluate is True, the simplified
    operands must be irreducible values (see isIrreducibleValue).
    '''
    # Any of the operands that can be simplified must be replaced with their evaluation
    from proveit import InnerExpr
    assert isinstance(innerExpr, InnerExpr), "Expecting 'innerExpr' to be of type 'InnerExpr'"
    inner = innerExpr.exprHierarchy[-1]
    while True:
        allReduced = True
        for operand in inner.operands:
            if not mustEvaluate or not isIrreducibleValue(operand):
                # the operand is not an irreducible value so it must be evaluated
                operandEval = operand.evaluation(assumptions=assumptions) if mustEvaluate else operand.simplification(assumptions=assumptions)
                if mustEvaluate and not isIrreducibleValue(operandEval.rhs):
                    raise EvaluationError('Evaluations expected to be irreducible values')
                if operandEval.lhs != operandEval.rhs:
                    # compose map to replace all instances of the operand within the inner expression
                    lambdaMap = innerExpr.replMap().compose(Lambda.globalRepl(inner, operand))
                    # substitute in the evaluated value
                    if inPlace:
                        innerExpr = InnerExpr(operandEval.subRightSideInto(lambdaMap), innerExpr.innerExprPath)
                    else:
                        innerExpr = InnerExpr(operandEval.substitution(lambdaMap).rhs, innerExpr.innerExprPath)
                    allReduced = False
                    break # start over (there may have been multiple substitutions)
        if allReduced: return innerExpr
        inner = innerExpr.exprHierarchy[-1]

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
        expr.evaluation(assumptions)
        return expr.prove(assumptions)
    # reduce the operands
    reducedExpr = reduceOperands(expr, assumptions)
    # prove the reduced version
    knownTruth = reducedExpr.prove(assumptions)
    # now rebuild the original via subLeftSideInto (for a shorter proof than substitutions)
    for k, operand in enumerate(expr.operands):
        # for each operand, replace it with the original
        subExprRepl = SubExprRepl(knownTruth).operands[k]
        knownTruth = operand.evaluation(assumptions=assumptions).subLeftSideInto(subExprRepl, assumptions)
    assert knownTruth.expr == expr, 'Equivalence substitutions did not work out as they should have'
    return knownTruth
"""
            
def defaultSimplification(innerExpr, inPlace=False, mustEvaluate=False, operandsOnly=False, assumptions=USE_DEFAULTS, automation=True):
    '''
    Default attempt to simplify the given inner expression under the given assumptions.
    If successful, returns a KnownTruth (using a subset of the given assumptions)
    that expresses an equality between the expression (on the left) and one with 
    a simplified form for the "inner" part (in some canonical sense determined by 
    the Operation).
    If inPlace is True, the top-level expression must be a KnownTruth
    and the simplified KnownTruth is derived instead of an equivalence
    relation.
    If mustEvaluate=True, the simplified form must be an irreducible value
    (see isIrreducibleValue).  Specifically, this method checks to see if an
    appropriate simplification/evaluation has already been proven.  If not, but
    if it is an Operation, call the simplification/evaluation method on
    all operands, make these substitions, then call simplification/evaluation on the
    expression with operands substituted for simplified forms.  It also treats, 
    as a special case, evaluating the expression to be true if it is in the set
    of assumptions [also see KnownTruth.evaluation and evaluateTruth].
    If operandsOnlTrue, only simplify the operands of the inner expression.
    '''
    from proveit.logic import TRUE, FALSE
    from proveit.logic.boolean._axioms_ import trueAxiom
    topLevel = innerExpr.exprHierarchy[0]
    inner = innerExpr.exprHierarchy[-1]
    if operandsOnly:
        # just do the reduction of the operands at the level below the "inner expression"
        reducedInnerExpr = reduceOperands(innerExpr, inPlace, mustEvaluate, assumptions) # OR DO WE WANT TO REDUCE AT THE INNER LEVEL??
        if inPlace:
            return reducedInnerExpr.exprHierarchy[0].prove(assumptions) # should have already been proven within 'reduceOperands' called above.
        return Equals(topLevel, reducedInnerExpr.exprHierarchy[0]).prove(assumptions) # should have already been proven within 'reduceOperands' called above.
    def innerSimplification(innerEquivalence):
        if inPlace:
            return innerEquivalence.subRightSideInto(innerExpr, assumptions=assumptions)
        return innerEquivalence.substitution(innerExpr, assumptions=assumptions)
    if isinstance(inner, IrreducibleValue):
        IrreducibleValue.evaluation(inner)
    assumptionsSet = set(defaults.checkedAssumptions(assumptions))
    # see if the expression is already known to be true as a special case
    try:
        inner.prove(assumptionsSet, automation=False)
        trueEval = evaluateTruth(inner, assumptionsSet) # A=TRUE given A
        if inner==topLevel:
            if inPlace: return trueAxiom
            else: return trueEval
        return innerSimplification(trueEval)
    except:
        pass
    # see if the negation of the expression is already known to be true as a special case
    try:
        inner.disprove(assumptionsSet, automation=False)
        falseEval = evaluateFalsehood(inner, assumptionsSet) # A=FALSE given Not(A)
        return innerSimplification(falseEval)
    except:
        pass
    # See if the expression already has a proven evaluation
    if inner in Equals.evaluations or (not mustEvaluate and inner in Equals.simplifications):
        simplifications = Equals.evaluations[inner] if mustEvaluate else Equals.simplifications[inner]
        candidates = []
        for knownTruth in simplifications:
            if knownTruth.isSufficient(assumptionsSet):
                candidates.append(knownTruth) # found existing evaluation suitable for the assumptions
        if len(candidates) >= 1:
            # return the "best" candidate with respect to fewest number of steps
            evaluation = min(candidates, key=lambda knownTruth: knownTruth.proof().numSteps)
            return innerSimplification(evaluation)
            
    if not automation:
        raise EvaluationError('Unknown evaluation (without automation): ' + str(inner))
    # See if the expression is equal to something that has an evaluation or is 
    # already known to be true.
    if inner in Equals.knownEqualities:
        for knownTruth in Equals.knownEqualities[inner]:
            try:
                if knownTruth.isSufficient(assumptionsSet):
                    if inPlace: # should first substitute in the known equivalence then simplify that
                        if inner == knownTruth.lhs:
                            knownTruth.subRightSideInto(innerExpr, assumptions)
                        elif inner == knownTruth.rhs:
                            knownTruth.subLeftSideInto(innerExpr, assumptions)
                    equivSimp = defaultSimplification(knownTruth.otherSide(inner).innerExpr(), inPlace=inPlace, mustEvaluate=mustEvaluate, assumptions=assumptions, automation=False)
                    if inPlace: return equivSimp # returns KnownTruth with simplification
                    innerEquiv = Equals(inner, equivSimp.rhs).concludeViaTransitivity(assumptions=assumptions) 
                    if inner == topLevel: return innerEquiv
                    return innerEquiv.substitution(innerExpr, assumptions=assumptions)
            except EvaluationError:
                pass     
    # try to simplify via reduction
    if not isinstance(inner, Operation):
        if mustEvaluate:
            raise EvaluationError('Unknown evaluation: ' + str(inner))
        else:
            # don't know how to simplify, so keep it the same
            return innerSimplification(Equals(inner, inner).prove())
    reducedInnerExpr = reduceOperands(innerExpr, inPlace, mustEvaluate, assumptions) # OR DO WE WANT TO REDUCE AT THE INNER LEVEL??
    if reducedInnerExpr == innerExpr:
        if mustEvaluate:
            # since it wasn't irreducible to begin with, it must change in order to evaluate
            raise EvaluationError('Unable to evaluate: ' + str(inner))
        elif inPlace:
            return topLevel # don't know how to simplify further
        else:
            return Equals(topLevel, topLevel).prove() # don't know how to simplify further
    # evaluate/simplify the reduced inner expression
    inner = reducedInnerExpr.exprHierarchy[-1]
    innerEquiv = inner.evaluation() if mustEvaluate else inner.simplification()
    value = innerEquiv.rhs
    if value == TRUE:
        # Attempt to evaluate via proving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluateTruth(inner, assumptions)
        except:
            pass
    if value == FALSE:
        # Attempt to evaluate via disproving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluateFalsehood(inner, assumptions)
        except:
            pass
    reducedSimplification = innerSimplification(innerEquiv)
    if inPlace:
        simplification = reducedSimplification
    else:
        # via transitivity, go from the original expression to the reduced expression 
        # (simplified inner operands) and then the final simplification (simplified inner
        # expression).
        simplification = Equals(topLevel, reducedSimplification.rhs).concludeViaTransitivity(assumptions)
    if not inPlace and topLevel==inner:
        # store direct simplifications in the simplifications dictionary for next time
        Equals.simplifications.setdefault(topLevel).add(simplification)
        if isinstance(value, IrreducibleValue):
            # also store it in the evaluations dictionary for next time
            # since it evaluated to an irreducible value.
            Equals.evaluations.setdefault(topLevel).add(simplification)
    return simplification  

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
    Returns the resulting KnownTruth evaluation if successful.
    '''
    from proveit.logic import FALSE
    return Equals(expr, FALSE).prove(assumptions)

class EvaluationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class InversionError(Exception):
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