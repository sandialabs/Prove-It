from proveit import OperationOverInstances, tryDerivation
from proveit import Literal, Operation, MultiVariable, Etcetera, USE_DEFAULTS
from proveit.common import P, Q, S, xMulti

NOTEXISTS = Literal(__package__, stringFormat='notexists', latexFormat=r'\nexists')

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=None, conditions=tuple()):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | conditions} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpr, domain, conditions)

    @classmethod
    def operatorOfOperation(subClass):
        return NOTEXISTS    
        
    def deriveSideEffects(self, knownTruth):
        '''
        Automatically derive the unfolded version, Not(Exists_{x | Q(x)} P(x)) from NotExists_{x | Q(x)} P(x).
        '''
        tryDerivation(self.unfold, knownTruth.assumptions)
        
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return Not(Exists_{x | Q(x)} P(x)) from NotExists_{x | Q(x)} P(x)
        '''
        from _theorems_ import notExistsUnfolding
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        return notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.instanceVars, S:self.domain}).deriveConclusion(assumptions)
    
    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) assuming Not(Exists_{x | Q(x)} P(x)).
        This is automatically derived; see Not.deriveSideEffects(..) and Not.deriveNotExists(..).
        '''
        from _theorems_ import notExistsFolding
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        folding = notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.instanceVars, S:self.domain})
        return folding.deriveConclusion(assumptions)

    """
    # MUST BE UPDATED
    def concludeViaForall(self):
        '''
        Prove and return either some NotExists_{x | Q(x)} Not(P(x)) or NotExists_{x | Q(x)} P(x)
        assuming forall_{x | Q(x)} P(x) or assuming forall_{x | Q(x)} (P(x) != TRUE) respectively.
        '''
        from _theorems_ import forallImpliesNotExistsNot, existsDefNegation
        from proveit.logic.equality.eqOps import NotEquals
        from boolOps import Not
        from boolSet import TRUE
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        operand = self.operans[0]
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.etcExpr
            assumption = Forall(operand.arguments, operand.expression.etcExpr, operand.domainCondition)
            return forallImpliesNotExistsNot.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveConclusion().checked({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            assumption = Forall(operand.arguments, NotEquals(operand.expression, TRUE), operand.domainCondition)
            return existsDefNegation.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveLeftViaEquivalence().checked({assumption})
    """

