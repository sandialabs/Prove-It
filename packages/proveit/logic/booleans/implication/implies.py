from proveit import Literal, Operation, defaults, USE_DEFAULTS, compositeExpression, ProofFailure
from proveit.logic.booleans.negation import Not
from proveit._common_ import A, B, C
from proveit import TransitiveRelation

class Implies(TransitiveRelation):
    _operator_ = Literal(stringFormat='=>', latexFormat=r'\Rightarrow', theory=__file__)

    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()

    def __init__(self, antecedent, consequent):
        TransitiveRelation.__init__(self, Implies._operator_, antecedent, consequent)
        self.antecedent = antecedent
        self.consequent = consequent

    @staticmethod
    def WeakRelationClass():
        '''
        The Strong and Weak form of transitive relations are the same for implication.
        It counts as a weak form because (A => A) is always true.
        '''
        return Implies

    @staticmethod
    def StrongRelationClass():
        '''
        The Strong and Weak form of transitive relations are the same for implication.
        '''
        return Implies

    def sideEffects(self, judgment):
        '''
        Yield the TransitiveRelation side-effects (which also records
        knownLeftSides nd knownRightSides).  Also derive the consequent
        as a side-effect if the antecedent is known to be true
        (under the "side-effect" assumptions).
        As a special case, if the consequent is FALSE, do
        deriveViaContradiction.
        '''
        from proveit.logic.booleans._common_ import FALSE
        for sideEffect in TransitiveRelation.sideEffects(self, judgment):
            yield sideEffect
        if self.antecedent.proven():
            yield self.deriveConsequent # B given A=>B and A
        if self.consequent == FALSE:
            yield self.deriveViaContradiction # Not(A) given A=>FALSE or A given Not(A)=>FALSE

    def negationSideEffects(self, judgment):
        '''
        Side-effect derivations to attempt automatically when an implication is negated.
        implemented by JML on 6/17/19
        '''
        yield self.deduceNegatedLeftImpl # Not(A <=> B) given Not(B => A)
        yield self.deduceNegatedRightImpl # Not(A <=> B) given Not(A => B)
        yield self.deduceNegatedReflex # B => A given Not(A => B)

    def conclude(self, assumptions):
        '''
        Try to automatically conclude this implication by reducing its
        operands to true/false, or by doing a "transitivity" search
        amongst known true implications whose assumptions are covered by
        the given assumptions.
        '''
        from ._theorems_ import (
                trueImpliesTrue, falseImpliesTrue, falseImpliesFalse, 
                falseAntecedentImplication, falsifiedAntecedentImplication,
                untrueAntecedentImplication)
        from proveit.logic import TRUE, FALSE, NotEquals, EvaluationError
        if self.antecedent == self.consequent:
            return self.concludeSelfImplication()

        if self in {trueImpliesTrue, falseImpliesTrue, falseImpliesFalse}:
            # should be proven via one of the imported theorems as a simple special case
            try:
                return self.evaluation(assumptions)
            except:
                return self.prove()
        
        if self.antecedent == FALSE:
            # The antecedent is FALSE, so we should try to prove the 
            # implication via falseAntecedentImplication.
            return falseAntecedentImplication.instantiate(
                    {A:self.consequent}, assumptions=assumptions)
        elif NotEquals(self.antecedent, TRUE).proven(assumptions):
            # The antecedent is known to be not equal to true, so
            # prove the implication via untrueAntecedentImplication.
            return untrueAntecedentImplication.instantiate(
                    {A:self.antecedent, B:self.consequent},
                    assumptions=assumptions)
        elif (self.antecedent.disproven(assumptions) or
              self.consequent.disproven(assumptions)):
            # Either the consequent or the antecedent has been disproven 
            # so we should try to prove the implication via 
            # falsifiedAntecedentImplication.
            return falsifiedAntecedentImplication.instantiate(
                    {A:self.antecedent, B:self.consequent},
                    assumptions=assumptions)
        elif self.consequent.proven(assumptions):
            # The consequent is proven, so we can prove the implication
            # via Deduction.
            return self.consequent.prove(assumptions).asImplication(
                    self.antecedent)
        
        try:
            antecedent_eval = self.antecedent.evaluated(assumptions)
            if antecedent_eval == FALSE:
                # try again with the antecedent disproven
                return self.conclude(assumptions)
        except (EvaluationError, ProofFailure):
            pass

        try:
            consequent_eval = self.consequent.evaluated(assumptions)
            if consequent_eval in (FALSE, TRUE):
                # try again with the consequent proven or disproven.
                return self.conclude(assumptions)
        except (EvaluationError, ProofFailure):
            pass
        
        try:
            # try to prove the implication via deduction.
            return self.consequent.prove(tuple(assumptions) + (self.antecedent,)).asImplication(self.antecedent)
        except ProofFailure:
            raise ProofFailure(self, assumptions,
                               "Unable to automatically conclude by "
                               "standard means.  To try to prove this via "
                               "transitive implication relations, try "
                               "'concludeViaTransitivity'.")

    def concludeNegation(self, assumptions=USE_DEFAULTS):
        '''
        Try to conclude True when Not(TRUE => FALSE) is called.
        implemented by JML on 6/18/19
        '''
        from proveit.logic.booleans._common_ import FALSE, TRUE
        try:
            if self.antecedent == TRUE and self.consequent == FALSE:
                from ._theorems_ import trueImpliesFalseNegated
        except:
            pass

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        '''
        From A => B return A => Not(Not(B)).
        implemented by JML on 6/18/19
        '''
        from ._theorems_ import doubleNegateConsequent
        if isinstance(self.consequent.operand, Not):
            return doubleNegateConsequent.instantiate({A: self.antecedent, B: self.consequent.operand.operand}, assumptions=assumptions)
        return "Not of the form 'A => B'"


    def deriveConsequent(self, assumptions=USE_DEFAULTS):
        r'''
        From A => B derive and return B assuming A.
        '''
        from proveit._core_.proof import ModusPonens
        return ModusPonens(self, assumptions).provenTruth

    def deriveIff(self, assumptions=USE_DEFAULTS):
        r'''
        From A => B derive and return A <=> B assuming B => A.
        '''
        from proveit.logic import Iff
        return Iff(self.A, self.B).concludeViaDefinition()

    def deduceNegatedRightImpl(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(A => B) derive and return Not(A <=> B).
        implemented by JML on 6/18/19
        '''
        from ._theorems_ import notIffViaNotRightImpl
        return notIffViaNotRightImpl.instantiate({A:self.antecedent, B:self.consequent},assumptions=assumptions)

    def deduceNegatedLeftImpl(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(B => A) derive and return Not(A <=> B).
        implemented by JML on 6/18/19
        '''
        from ._theorems_ import notIffViaNotLeftImpl
        return notIffViaNotLeftImpl.instantiate({B: self.antecedent, A: self.consequent}, assumptions=assumptions)

    def deduceNegatedReflex(self, assumptions=USE_DEFAULTS):
        #implemented by JML on 6/18/19
        from ._theorems_ import negatedReflex
        return negatedReflex.instantiate({A:self.antecedent, B:self.consequent},assumptions=assumptions)

    def denyAntecedent(self, assumptions=USE_DEFAULTS):
        '''
        From A => B, derive and return Not(A) assuming Not(B).
        '''
        from ._theorems_ import modusTollensAffirmation, modusTollensDenial
        if isinstance(self.antecedent,  Not):
            return modusTollensAffirmation.instantiate({A:self.antecedent.operand, B:self.consequent}, assumptions=assumptions)
        else:
            return modusTollensDenial.instantiate({A:self.antecedent, B:self.consequent}, assumptions=assumptions)

    def applyTransitivity(self, otherImpl, assumptions=USE_DEFAULTS):
        '''
        From :math:`A \Rightarrow B` (self) and a given :math:`B \Rightarrow C` (otherImpl), derive and return :math:`A \Rightarrow C`.
        '''
        from ._theorems_ import implicationTransitivity
        if self.consequent == otherImpl.antecedent:
            return implicationTransitivity.instantiate({A:self.antecedent, B:self.consequent, C:otherImpl.consequent}, assumptions=assumptions)
        elif self.antecedent == otherImpl.consequent:
            return implicationTransitivity.instantiate({A:otherImpl.antecedent, B:self.antecedent, C:self.consequent}, assumptions=assumptions)

    def deriveViaContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From (Not(A) => FALSE), derive and return A assuming A in Boolean.
        Or from (A => FALSE), derive and return Not(A) assuming A in Boolean.
        Or from (A => FALSE), derive and return A != TRUE.
        '''
        from proveit.logic import FALSE, inBool
        from ._axioms_ import affirmViaContradiction, denyViaContradiction
        from ._theorems_ import notTrueViaContradiction
        if self.consequent != FALSE:
            raise ValueError('deriveViaContradiction method is only applicable if FALSE is implicated, not for ' + str(self))
        if isinstance(self.antecedent, Not):
            stmt = self.antecedent.operand
            return affirmViaContradiction.instantiate({A:stmt}, assumptions=assumptions)
        else:
            if inBool(self.antecedent).proven(assumptions):
                return denyViaContradiction.instantiate({A:self.antecedent}, assumptions=assumptions)
            else:
                return notTrueViaContradiction.instantiate({A:self.antecedent},assumptions=assumptions)

    def concludeSelfImplication(self):
        from ._theorems_ import selfImplication
        if self.antecedent != self.consequent:
            raise ValueError('May only conclude a self implementation when the antecedent and consequent are the same')
        return selfImplication.instantiate({A:self.antecedent})

    def generalize(self, forallVars, domain=None, conditions=tuple()):
        r'''
        This makes a generalization of this expression, prepending Forall
        operations according to newForallVars and newConditions and/or newDomain
        that will bind 'arbitrary' free variables.  This overrides the expr
        version to absorb antecedent into conditions if they match.  For example,
        :math:`[A(x) \Rightarrow [B(x, y) \Rightarrow P(x, y)]]` generalized
        forall :math:`x, y` such that :math:`A(x), B(x, y)`
        becomes :math:`\forall_{x, y | A(x), B(x, y)} P(x, y)`,
        '''
        from proveit.logic import InSet
        hypothesizedConditions = set()
        conditionsSet = set(compositeExpression(conditions))
        if domain is not None:
            # add in the effective conditions from the domain
            for var in compositeExpression(forallVars):
                conditionsSet.add(InSet(var, domain))
        expr = self
        while isinstance(expr, Implies) and expr.antecedent in conditionsSet:
            hypothesizedConditions.add(expr.antecedent)
            expr = expr.consequent
        if len(hypothesizedConditions) == 0:
            # Just use the expr version
            return expr.generalize(self, forallVars, domain, conditions)
        return expr.generalize(expr, forallVars, domain, conditions)
        #return Forall(newForallVars, expr, newConditions)

    def contrapose(self, assumptions=USE_DEFAULTS):
        '''
        Depending upon the form of self with respect to negation of the antecedent and/or consequent,
        will derive from self and return as follows:

        * From :math:`[\lnot A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[\lnot A \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        '''
        from ._theorems_ import fromContraposition, toContraposition, contraposeNegConsequent, contraposeNegAntecedent
        from proveit.logic import Not
        if isinstance(self.antecedent, Not) and isinstance(self.consequent, Not):
            return fromContraposition.instantiate({B:self.antecedent.operand, A:self.consequent.operand}, assumptions=assumptions)
        elif isinstance(self.antecedent, Not):
            return contraposeNegAntecedent.instantiate({A:self.antecedent.operand, B:self.consequent}, assumptions=assumptions)
        elif isinstance(self.consequent, Not):
            return contraposeNegConsequent.instantiate({A:self.antecedent, B:self.consequent.operand}, assumptions=assumptions)
        else:
            return toContraposition.instantiate({A:self.antecedent, B:self.consequent}, assumptions=assumptions)

    def evaluation(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE.
        '''
        # load in truth-table evaluations
        from ._axioms_ import impliesTF
        from ._theorems_ import impliesTT, impliesFT, impliesFF
        return Operation.evaluation(self, assumptions, automation=automation)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        from ._theorems_ import implicationClosure
        return implicationClosure.instantiate({A:self.antecedent, B:self.consequent}, assumptions=assumptions)

def concludeViaImplication(consequent, assumptions):
    '''
    Perform a breadth-first search of implications going in reverse from the consequent
    until reaching an antecedent that has been proven.
    '''
    visited = set()
    consequent_map = dict() # map antecedents to consequents that arise durent the breadth-first search
    queue = [consequent]
    while len(queue) > 0:
        expr = queue.pop()
        if expr not in visited:
            visited.add(expr)
            if expr not in Implies.knownRightSides:
                continue # no known implications with the expr as the consequent; skip it
            for knownImplication in Implies.knownRightSides[expr]:
                # see if the knownImplication is applicable under the given set of assumptions
                if knownImplication.isSufficient(assumptions):
                    local_antecedent, local_consequent = knownImplication.antecedent, knownImplication.consequent
                    consequent_map[local_antecedent] = local_consequent
                    try:
                        knownImplication.antecedent.prove(assumptions, automation=False)
                        # found a solution; use it by deriving "local" consequents until getting to the desired consequent
                        while True:
                            judgment = Implies(local_antecedent, local_consequent).deriveConsequent(assumptions=assumptions)
                            if judgment.expr == consequent:
                                return judgment
                            local_antecedent = judgment.expr
                            local_consequent = consequent_map[local_antecedent]
                    except ProofFailure:
                        queue.append(local_antecedent)
    raise ProofFailure(consequent, assumptions, 'Unable to conclude via implications')

def affirmViaContradiction(contradictoryExpr, conclusion, assumptions):
    '''
    Affirms the conclusion via reductio ad absurdum.
    First calls deriveContradiction on the contradictoryExpr to derive FALSE,
    then derive the conclusion after proving that the negated conclusion
    implies FALSE.  The conclusion must be a Boolean.
    '''
    from proveit.logic import Not
    assumptions = defaults.checkedAssumptions(assumptions)
    extendedAssumptions = assumptions + (Not(conclusion),)
    return contradictoryExpr.deriveContradiction(extendedAssumptions).asImplication(Not(conclusion)).deriveViaContradiction(assumptions)

def denyViaContradiction(contradictoryExpr, conclusion, assumptions):
    '''
    Deny the conclusion (affirm its negation) via reductio ad absurdum.
    First calls deriveContradiction on the contradictoryExpr to derive FALSE,
    then derive the negated conclusion after proving that the conclusion itself
    implies FALSE.  The conclusion must be a Boolean.
    '''
    from proveit.logic import Not
    assumptions = defaults.checkedAssumptions(assumptions)
    extendedAssumptions = assumptions + (conclusion,)
    return contradictoryExpr.deriveContradiction(extendedAssumptions).asImplication(conclusion).deriveViaContradiction(assumptions)