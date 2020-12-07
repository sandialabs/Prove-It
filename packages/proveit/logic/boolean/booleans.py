from proveit import Operation, Literal, USE_DEFAULTS, ProofFailure
from proveit.logic.irreducible_value import IrreducibleValue
from proveit.logic.set_theory.membership import Membership, Nonmembership
from proveit._common_ import A, C, P, Q

class BooleanSet(Literal):
    def __init__(self):
        Literal.__init__(self, stringFormat='BOOLEANS', latexFormat=r'\mathbb{B}')
    
    def membershipObject(self, element):
        return BooleanMembership(element)

    def nonmembershipObject(self, element):
        return BooleanNonmembership(element)
    
    def forallEvaluation(self, forallStmt, assumptions=USE_DEFAULTS):
        '''
        Given a forall statement over the BOOLEANS domain, evaluate to TRUE or FALSE
        if possible.
        updated by JML 6/28/19
        '''        
        from proveit.logic import Forall, Equals, SimplificationError
        from ._theorems_ import falseEqFalse, trueEqTrue 
        from ._theorems_ import forallBoolEvalTrue, forallBoolEvalFalseViaTF, forallBoolEvalFalseViaFF, forallBoolEvalFalseViaFT
        from ._common_ import TRUE, FALSE, Boolean
        from .conjunction import compose
        assert(isinstance(forallStmt, Forall)), "May only apply forallEvaluation method of BOOLEANS to a forall statement"
        assert(forallStmt.domain == Boolean), "May only apply forallEvaluation method of BOOLEANS to a forall statement with the BOOLEANS domain"
        instanceList = list(forallStmt.instanceParamLists())
        instanceVar = instanceList[0][0]
        instanceExpr = forallStmt.instanceExpr
        P_op = Operation(P, instanceVar)
        trueInstance = instanceExpr.replaced({instanceVar:TRUE})
        falseInstance = instanceExpr.replaced({instanceVar:FALSE})
        if trueInstance == TRUE and falseInstance == FALSE:
            # special case of Forall_{A in BOOLEANS} A
            falseEqFalse # FALSE = FALSE
            trueEqTrue # TRUE = TRUE
            return forallBoolEvalFalseViaTF.instantiate({P_op:instanceExpr}).deriveConclusion()
        else:
            # must evaluate for the TRUE and FALSE case separately
            evalTrueInstance = trueInstance.evaluation(assumptions)
            evalFalseInstance = falseInstance.evaluation(assumptions)
            if not isinstance(evalTrueInstance.expr, Equals) or not isinstance(evalFalseInstance.expr, Equals):
                raise SimplificationError('Quantified instances must produce equalities as evaluations')            
            # proper evaluations for both cases (TRUE and FALSE)
            trueCaseVal = evalTrueInstance.rhs
            falseCaseVal = evalFalseInstance.rhs
            if trueCaseVal == TRUE and falseCaseVal == TRUE:
                # both cases are TRUE, so the forall over booleans is TRUE
                compose([evalTrueInstance.deriveViaBooleanEquality(), evalFalseInstance.deriveViaBooleanEquality()], assumptions)
                forallBoolEvalTrue.instantiate({P_op:instanceExpr, A:instanceVar})
                return forallBoolEvalTrue.instantiate({P_op:instanceExpr, A:instanceVar}, assumptions=assumptions).deriveConclusion(assumptions)
            else:
                # one case is FALSE, so the forall over booleans is FALSE
                compose([evalTrueInstance, evalFalseInstance], assumptions)
                if trueCaseVal == FALSE and falseCaseVal == FALSE:
                    return forallBoolEvalFalseViaFF.instantiate({P_op:instanceExpr, A:instanceVar}, assumptions=assumptions).deriveConclusion(assumptions)
                elif trueCaseVal == FALSE and falseCaseVal == TRUE:
                    return forallBoolEvalFalseViaFT.instantiate({P_op:instanceExpr, A:instanceVar}, assumptions=assumptions).deriveConclusion(assumptions)
                elif trueCaseVal == TRUE and falseCaseVal == FALSE:
                    return forallBoolEvalFalseViaTF.instantiate({P_op:instanceExpr, A:instanceVar}, assumptions=assumptions).deriveConclusion(assumptions)
                else:
                    raise SimplificationError('Quantified instance evaluations must be TRUE or FALSE')         
    
    def unfoldForall(self, forallStmt, assumptions=USE_DEFAULTS):
        '''
        Given forall_{A in Boolean} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall
        from ._theorems_ import unfoldForallOverBool
        from ._common_ import Boolean
        assert(isinstance(forallStmt, Forall)), "May only apply unfoldForall method of Boolean to a forall statement"
        assert(forallStmt.domain == Boolean), "May only apply unfoldForall method of Boolean to a forall statement with the Boolean domain"
        Px = Operation(P, forallStmt.instanceVar)
        _Px = forallStmt.instanceExpr
        _A = forallStmt.instanceVar
        return unfoldForallOverBool.instantiate(
                {Px:_Px, A:_A}, assumptions=assumptions)

    def foldAsForall(self, forallStmt, assumptions=USE_DEFAULTS):
        '''
        Given forall_{A in Boolean} P(A), conclude and return it from 
        [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall, And
        from ._theorems_ import foldForallOverBool, foldConditionedForallOverBool
        from ._common_ import Boolean
        assert(isinstance(forallStmt, Forall)), "May only apply foldAsForall method of Boolean to a forall statement"
        assert(forallStmt.domain == Boolean), "May only apply foldAsForall method of Boolean to a forall statement with the Boolean domain"
        if(len(forallStmt.conditions)>1):
            if len(forallStmt.conditions)==2:
                condition = forallStmt.conditions[1]
            else:
                condition = And(*forallStmt.conditions[1:])
            Qx = Operation(Q, forallStmt.instanceVar)
            _Qx = condition
            Px = Operation(P, forallStmt.instanceVar)
            _Px = forallStmt.instanceExpr
            _A = forallStmt.instanceVar
            return foldConditionedForallOverBool.instantiate(
                    {Qx:_Qx, Px:_Px, A:_A}, num_forall_eliminations=1,
                    assumptions=assumptions)
        else:
            # forall_{A in Boolean} P(A), assuming P(TRUE) and P(FALSE)
            Px = Operation(P, forallStmt.instanceVar)
            _Px = forallStmt.instanceExpr
            _A = forallStmt.instanceVar
            return foldForallOverBool.instantiate(
                    {Px:_Px, A:_A}, num_forall_eliminations=1,
                    assumptions=assumptions)

class BooleanMembership(Membership):
    '''
    Defines methods that apply to InSet(element, Boolean) objects
    via InSet.__getattr__ which calls Boolean.membershipObject(element)
    to return a BooleanMembership object.
    '''
    
    def __init__(self, element):
        Membership.__init__(self, element)
    
    def sideEffects(self, judgment):
        '''
        Yield side-effect methods to try when the element is proven to be in the set of Boolean
        by calling 'inBoolSideEffects' on the element if it has such a method.
        Edited by JML on 6/27/19 to add foldInBool sideEffect
        '''
        from proveit.logic.boolean._theorems_ import unfoldInBool, foldInBool
        if hasattr(self.element, 'inBoolSideEffects'):
            for sideEffect in self.element.inBoolSideEffects(judgment):
                yield sideEffect
        # don't automatically do unfoldInBoolExplicit if unfoldInBool is unusable -- avoids infinite recursion
        if unfoldInBool.isUsable():
            yield self.unfold
    
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the set of Boolean under the given assumptions.
        '''   
        from ._theorems_ import inBoolIfTrue, inBoolIfFalse
        element = self.element
        # if the element is already proven or disproven, use inBoolIfTrue or inBoolIfFalse
        try:
            element.prove(assumptions=assumptions, automation=False)
            return inBoolIfTrue.instantiate({A:element}, assumptions=assumptions)
        except ProofFailure:
            pass
        try:
            element.disprove(assumptions=assumptions, automation=False)
            return inBoolIfFalse.instantiate({A:element}, assumptions=assumptions)
        except ProofFailure:
            pass
        # Use 'deduceInBool' if the element has that method.
        if hasattr(element, 'deduceInBool'):
            return element.deduceInBool(assumptions=assumptions)
        raise ProofFailure(inBool(element), assumptions, str(element) + ' not proven to be equal to TRUE or FALSE.')

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce [(element in Boolean) = [(element = TRUE) or (element = FALSE)].
        '''
        from ._theorems_ import inBoolDef
        return inBoolDef.instantiate({A:self.element})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From inBool(Element), derive and return [element or not(element)] if
        unfoldInBool is usable.  It it is not, instead try to derive and return
        [(element=TRUE) or (element=FALSE)].
        '''
        from ._theorems_ import unfoldInBool, unfoldInBoolExplicit
        if unfoldInBool.isUsable():
            #  [element or not(element)] assuming inBool(element)
            return unfoldInBool.instantiate({A:self.element}, assumptions=assumptions)
        else:
            #  [(element = TRUE) or (element = FALSE)] assuming inBool(element)
            return unfoldInBoolExplicit.instantiate({A:self.element}, assumptions=assumptions)

    def fold(self, assumptions=USE_DEFAULTS):
        '''
        From [(element=TRUE) or (element=FALSE)], derive inBool(Element).
        Created by JML on 6/27/19 for foldInBool sideEffect
        '''
        from ._theorems_ import foldInBool
        if foldInBool.isUsable():
            return foldInBool.instantiate({A:self.element}, assumptions=assumptions)

    def deriveViaExcludedMiddle(self, consequent, assumptions=USE_DEFAULTS):
        '''
        Derive the consequent from (element in Boolean)
        given element => consequent and Not(element) => consequent.
        '''
        from ._theorems_ import fromExcludedMiddle
        return fromExcludedMiddle.instantiate({A:self.element, C:consequent}, assumptions=assumptions)
    
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import inBoolInBool
        return inBoolInBool.instantiate({A:self.element})
    

class BooleanNonmembership(Nonmembership):
    
    def __init__(self, element):
        Nonmembership.__init__(self)

    def equivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Derive [(element not in Boolean) = [(element != TRUE) and (element != FALSE)].
        '''
        from ._theorems_ import notInBoolEquiv
        return notInBoolEquiv.instantiate({A:element})


class TrueLiteral(Literal, IrreducibleValue):
    def __init__(self):
        Literal.__init__(self, stringFormat='TRUE', latexFormat=r'\top')
    
    def conclude(self, assumptions):
        from ._axioms_ import trueAxiom
        return trueAxiom
    
    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        from ._theorems_ import trueEqTrue, trueNotFalse
        from ._common_ import TRUE, FALSE
        if other == TRUE:
            return trueEqTrue.evaluation()
        elif other == FALSE:
            return trueNotFalse.unfold().equateNegatedToFalse()

    def notEqual(self, other, assumptions=USE_DEFAULTS):
        from ._theorems_ import trueNotFalse
        from ._common_ import TRUE, FALSE
        if other == FALSE:
            return trueNotFalse
        if other == TRUE:
            raise ProofFailure("Cannot prove TRUE != TRUE since that statement is false")
        raise ProofFailure("Inequality between TRUE and a non-boolean not defined")
        
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import trueInBool
        return trueInBool
        
class FalseLiteral(Literal, IrreducibleValue):
    def __init__(self):
        Literal.__init__(self, stringFormat='FALSE', latexFormat=r'\bot')
    
    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        from ._axioms_ import falseNotTrue
        from ._theorems_ import falseEqFalse
        from ._common_ import TRUE, FALSE
        if other == FALSE:
            return falseEqFalse.evaluation()
        elif other == TRUE:
            return falseNotTrue.unfold().equateNegatedToFalse()

    def concludeNegation(self, assumptions):
        from proveit.logic.boolean.negation._theorems_ import notFalse
        return notFalse # the negation of FALSE

    def notEqual(self, other, assumptions=USE_DEFAULTS):
        from _.theorems_ import falseNotTrue
        from ._common_ import TRUE, FALSE
        if other == TRUE:
            return falseNotTrue
        if other == FALSE:
            raise ProofFailure("Cannot prove FALSE != FALSE since that statement is false")
        raise ProofFailure("Inequality between FALSE and a non-boolean not defined")

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import falseInBool
        return falseInBool
    
    def denyAssumption(self, assumption_to_deny, assumptions=USE_DEFAULTS):
        '''
        If FALSE can be proven under a set of assumptions, any one
        of those assumptions may be proven untrue given the other
        assumptions.
        '''
        impl = self.prove(assumptions).asImplication(assumption_to_deny)
        return impl.denyAntecedent()

def inBool(*elements):
    from proveit.logic.set_theory import InSet
    from ._common_ import Boolean
    if len(elements) == 1:
        return InSet(elements[0], Boolean)
    return [InSet(element, Boolean) for element in elements]
