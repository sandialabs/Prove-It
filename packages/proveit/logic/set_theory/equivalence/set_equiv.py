from proveit import asExpression, USE_DEFAULTS, ProofFailure
from proveit import Literal
from proveit import TransitiveRelation, TransitivityException
from proveit.logic.irreducible_value import IrreducibleValue, isIrreducibleValue
from proveit._common_ import A, B, C, P, f, x, y, z

class SetEquiv(TransitiveRelation):
    '''
    Class to capture the membership equivalence of 2 sets A and B.
    SetEquiv(A, B) is a claim that all elements of A are also elements
    of B and vice-versa. The SetEquiv relation uses the congruence
    symbol to distinguish the SetEquiv claim from the stronger claim
    that A = B.
    '''
    # operator for the SetEquiv relation
    _operator_ = Literal(stringFormat='equiv', latexFormat=r'\cong',
                         theory=__file__)        
    
    # map Expressions to sets of Judgments of set equivalences that
    # involve the Expression on the left hand or right hand side.
    # knownEqualities = dict()
    knownEquivalences = dict()

    # Map Expressions to a subset of knownEquivalences that are 
    # deemed to effect simplifications of the inner expression
    # on the right hand side according to some canonical method 
    # of simplication determined by each operation.
    simplifications = dict()

    # Specific simplifications that simplify the inner expression to 
    # IrreducibleValue objects.
    evaluations = dict()
        
    # Record found inversions.  See the invert method.
    # Maps (lambda_map, rhs) pairs to a list of
    # (known_equivalence, inversion) pairs, recording previous results
    # of the invert method for future reference.
    inversions = dict()
    
    # Record the SetEquiv objects being initialized (to avoid infinite
    # recursion while automatically deducing an equality is in Booleans).
    initializing = set()

    def __init__(self, a, b):
        TransitiveRelation.__init__(self, SetEquiv._operator_, a, b)
        if self not in SetEquiv.initializing:
            SetEquiv.initializing.add(self)
            try:
                self.deduceInBool() # proactively prove (a equiv b) in Booleans.
            except:
                # may fail before the relevent _axioms_ have been generated
                pass # and that's okay            
            SetEquiv.initializing.remove(self)

    def sideEffects(self, judgment):
        '''
        Record the judgment in SetEquiv.knownEquivalences, associated
        from the left hand side and the right hand side.  This
        information may be useful for concluding new equivalences via
        transitivity. If the right hand side is an "irreducible value"
        (see isIrreducibleValue), also record it in SetEquiv.evaluations
        for use when the evaluation method is called. Some side-effects
        derivations are also attempted depending upon the form of
        this equivalence.
        '''
        from proveit.logic.boolean._common_ import TRUE, FALSE
        SetEquiv.knownEquivalences.setdefault(self.lhs, set()).add(judgment)
        SetEquiv.knownEquivalences.setdefault(self.rhs, set()).add(judgment)
        # not yet clear if the irreducible value check is relevant for sets
        # if isIrreducibleValue(self.rhs):
        #     SetEquiv.simplifications.setdefault(self.lhs, set()).add(judgment)
        #     SetEquiv.evaluations.setdefault(self.lhs, set()).add(judgment)
        if (self.lhs != self.rhs): # e.g. if we don't have SetEquiv(A, A)
            # automatically derive the reversed form which is equivalent
            yield self.deriveReversed
        # THE FOLLOWING SEEM INAPPLICABLE, because we are dealing with sets
        # if self.rhs == FALSE:
        #     # derive lhs => FALSE from lhs = FALSE
        #     yield self.deriveContradiction
        #     # derive lhs from Not(lhs) = FALSE, if self is in this form
        #     #yield self.deriveViaFalsifiedNegation
        # if self.rhs in (TRUE, FALSE):
        #     # automatically derive A from A=TRUE or Not(A) from A=FALSE
        #     yield self.deriveViaBooleanEquality
        # STILL CHECKING IN THE RELEVANCE OF THE FOLLOWING
        # if hasattr(self.lhs, 'equalitySideEffects'):
        #     for sideEffect in self.lhs.equalitySideEffects(judgment):
        #         yield sideEffect

    def negationSideEffects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a
        negated equivalence. IN PROGRESS     
        '''
        from proveit.logic.boolean._common_ import FALSE
        yield self.deduceNotEquiv # A not_equiv B from not(A equiv B)

    def conclude(self, assumptions):
        '''
        Attempt to conclude the equivalence in various ways:
        simple reflexivity (A equiv A), via an evaluation (if one side
        is an irreducible), or via transitivity.
        IN PROGRESS. NOT YET CLEAR how this applies to the SetEquiv
        '''
        if self.lhs==self.rhs:
            try:
                # Trivial A = A
                return self.concludeViaReflexivity(assumptions=assumptions)
            except:
                pass # e.g., reflexivity theorem may not be usable
        try:
            return self.concludeAsFolded(assumptions=assumptions)
        except ProofFailure:
            raise ProofFailure(self, assumptions,
                               "Unable to automatically conclude by "
                               "standard means.  To try to prove this via "
                               "transitive implication relations, try "
                               "'concludeViaTransitivity'.")        
        
    #     if self.lhs or self.rhs in (TRUE, FALSE):
    #         try:
    #             # Try to conclude as TRUE or FALSE.
    #             return self.concludeBooleanEquality(assumptions)
    #         except ProofFailure:
    #             pass
    #     if isIrreducibleValue(self.rhs):
    #         try:
    #             evaluation = self.lhs.evaluation(assumptions)
    #             if evaluation.rhs != self.rhs:
    #                 raise ProofFailure(self, assumptions, "Does not match with evaluation: %s"%str(evaluation))
    #             return evaluation
    #         except SimplificationError as e:
    #             raise ProofFailure(self, assumptions, "Evaluation error: %s"%e.message)
    #     elif isIrreducibleValue(self.lhs):
    #         try:
    #             evaluation = self.rhs.evaluation(assumptions)
    #             if evaluation.rhs != self.lhs:
    #                 raise ProofFailure(self, assumptions, "Does not match with evaluation: %s"%str(evaluation))
    #             return evaluation.deriveReversed()
    #         except SimplificationError as e:
    #             raise ProofFailure(self, assumptions, "Evaluation error: %s"%e.message)
    #     try:
    #         Implies(self.lhs, self.rhs).prove(assumptions, automation=False)
    #         Implies(self.rhs, self.lhs).prove(assumptions, automation=False)
    #         # lhs => rhs and rhs => lhs, so attempt to prove lhs = rhs via lhs <=> rhs
    #         # which works when they can both be proven to be Booleans.
    #         try:
    #             return Iff(self.lhs, self.rhs).deriveEquality(assumptions)
    #         except:
    #             from proveit.logic.boolean.implication._theorems_ import eqFromMutualImpl
    #             return eqFromMutualImpl.instantiate({A:self.lhs, B:self.rhs}, assumptions=assumptions)
    #     except ProofFailure:
    #         pass
        
    #     """
    #     # Use concludeEquality if available
    #     if hasattr(self.lhs, 'concludeEquality'):
    #         return self.lhs.concludeEquality(assumptions)
    #     if hasattr(self.rhs, 'concludeEquality'):
    #         return self.rhs.concludeEquality(assumptions)
    #     """
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return TransitiveRelation.conclude(self, assumptions)

    # @staticmethod
    # def knownRelationsFromLeft(expr, assumptionsSet):
    #     '''
    #     For each Judgment that is an Equals involving the given expression on
    #     the left hand side, yield the Judgment and the right hand side.
    #     '''
    #     for judgment in Equals.knownEqualities.get(expr, frozenset()):
    #         if judgment.lhs == expr:
    #             if judgment.isSufficient(assumptionsSet):
    #                 yield (judgment, judgment.rhs)
    
    # @staticmethod
    # def knownRelationsFromRight(expr, assumptionsSet):
    #     '''
    #     For each Judgment that is an Equals involving the given expression on
    #     the right hand side, yield the Judgment and the left hand side.
    #     '''
    #     for judgment in Equals.knownEqualities.get(expr, frozenset()):
    #         if judgment.rhs == expr:
    #             if judgment.isSufficient(assumptionsSet):
    #                 yield (judgment, judgment.lhs)

    def concludeViaReflexivity(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form A equiv A.
        '''
        from ._theorems_ import setEquivReflexivity
        assert self.lhs == self.rhs
        return setEquivReflexivity.instantiate(
                {A:self.lhs}, assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        From forall_{x} (x in A) = (x in B),
        conclude A set_equiv B.
        '''
        from ._theorems_ import setEquivFold
        return setEquivFold.instantiate({A:self.lhs, B:self.rhs},
                                        assumptions=assumptions)
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A set_equiv B derive
        forall_{x} (x in A) = (x in B) 
        '''
        from ._theorems_ import setEquivUnfold
        return setEquivUnfold.instantiate({A:self.lhs, B:self.rhs}, 
                                          assumptions=assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A set_equiv B derive B set_equiv A.
        This derivation is an automatic side-effect.
        '''
        from ._theorems_ import setEquivReversal
        return setEquivReversal.instantiate(
                {A:self.lhs, B:self.rhs}, assumptions=assumptions)

    def deduceNotEquiv(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A not_equiv B assuming not(A equiv B),
        where self is (A equiv B).
        '''
        from .set_not_equiv import SetNotEquiv
        return SetNotEquiv(self.lhs, self.rhs).concludeAsFolded(assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From A set_equiv B (self) and B set_equiv C (other) derive and
        return A set_equiv C.
        If "other" is not a SetEquiv, reverse roles and call
        'applyTransitivity' from the "other" side.
        This method initially based on the applyTransitivity method
        from Equals class. 
        '''
        from ._theorems_ import setEquivTransitivity
        other = asExpression(other)
        if not isinstance(other, SetEquiv):
            # If the other relation is not "SetEquiv",
            # call from the "other" side.
            return other.applyTransitivity(self, assumptions)
        otherSetEquiv = other
        # We can assume that B set_equiv A will be a Judgment if
        # A set_equiv B is a Judgment because it is derived as a
        # side-effect.
        if self.rhs == otherSetEquiv.lhs:
            return setEquivTransitivity.instantiate(
                    {A:self.lhs, B:self.rhs, C:otherSetEquiv.rhs},
                    assumptions=assumptions)
        elif self.rhs == otherSetEquiv.rhs:
            return setEquivTransitivity.instantiate(
                {A:self.lhs, B:self.rhs, C:otherSetEquiv.lhs},
                assumptions=assumptions)
        elif self.lhs == otherSetEquiv.lhs:
            return setEquivTransitivity.instantiate(
                {A:self.rhs, B:self.lhs, C:otherSetEquiv.rhs},
                assumptions=assumptions)
        elif self.lhs == otherSetEquiv.rhs:
            return setEquivTransitivity.instantiate(
                {A:self.rhs, B:self.lhs, C:otherSetEquiv.lhs},
                assumptions=assumptions)
        else:
            raise TransitivityException(
                    self, assumptions,
                    'Transitivity cannot be applied unless there is '
                    'something in common in the set equivalences: '
                    '%s vs %s'%(str(self), str(other)))

    def subLeftSideInto(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From A equiv B, and given P(B), derive P(A) assuming P(B).
        UNDER CONSTRUCTION, adapted from Equals class. 
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression upon
        which to perform a global replacement of self.rhs.
        '''
        from ._theorems_ import subLeftSideInto
        from proveit.logic import Equals
        Plambda = Equals._lambdaExpr(lambdaMap, self.rhs)

        return subLeftSideInto.instantiate(
                {A:self.lhs, B:self.rhs, P:Plambda}, assumptions=assumptions)

    def subRightSideInto(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        From A equiv B, and given P(A), derive P(B) assuming P(A).
        UNDER CONSTRUCTION, adapted from Equals class. 
        P(x) is provided via lambdaMap as a Lambda expression or an 
        object that returns a Lambda expression when calling lambdaMap()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression upon
        which to perform a global replacement of self.lhs.
        '''
        from ._theorems_ import subRightSideInto
        from proveit.logic import Equals
        Plambda = Equals._lambdaExpr(lambdaMap, self.lhs)
        return subRightSideInto.instantiate(
                {A:self.lhs, B:self.rhs, P:Plambda}, assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SetEquiv claim is in the set
        of Booleans.
        '''
        from ._theorems_ import setEquivInBool
        return setEquivInBool.instantiate({A:self.lhs, B:self.rhs},
                                         assumptions=assumptions)

    

