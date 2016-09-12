from proveit import OperationOverInstances
from proveit import Literal, Operation, ExpressionList, MultiVariable, Etcetera, USE_DEFAULTS
from proveit.common import P, Q, S

EXISTS = Literal(__package__, stringFormat='exists', latexFormat=r'\exists')

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=None, conditions=tuple()):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | condition} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpr, domain, conditions)

    @classmethod
    def operatorOfOperation(subClass):
        return EXISTS 
           
    def deriveSideEffects(self, knownTruth):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        self.deriveNegatedForall(knownTruth.assumptions)

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{..y.. in S | ..Q(..x..)..} P(..y..)] from P(..x..) and Q(..x..) and ..x.. in S, where ..x.. is the given exampleInstance.
        '''
        from theorems import existenceByExample
        from proveit.logic import InSet
        from proveit.common import xEtc, yEtc
        if len(self.instanceVars) > 1 and (not isinstance(exampleInstance, ExpressionList) or (len(exampleInstance) != len(self.instanceVars))):
            raise Exception('Number in exampleInstance list must match number of instance variables in the Exists expression')
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        # P(..x..) where ..x.. is the given exampleInstance
        exampleMapping = {instanceVar:exampleInstanceElem for instanceVar, exampleInstanceElem in zip(self.instanceVars, exampleInstance if isinstance(exampleInstance, ExpressionList) else [exampleInstance])}
        exampleExpr = self.instanceExpr.substituted(exampleMapping)
        # ..Q(..x..).. where ..x.. is the given exampleInstance
        exampleConditions = self.conditions.substituted(exampleMapping)
        if self.domain is not None:
            for iVar in self.instanceVars:
                exampleConditions.append(InSet(iVar, self.domain))
        # exists_{..y.. | ..Q(..x..)..} P(..y..)]
        return existenceByExample.specialize({P_op:P_op_sub, Q_op:Q_op_sub, yEtc:self.instanceVars, S:self.domain}).specialize({xEtc:exampleInstance}).deriveConclusion().checked({exampleExpr, exampleConditions})

    def deriveNegatedForall(self, assumptions=USE_DEFAULTS):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        from axioms import existsDef
        from theorems import existsNotImpliesNotForall
        from proveit.logic import Not
        from proveit.common import xEtc        
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.operand
            return existsNotImpliesNotForall.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).deriveConclusion(assumptions)
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            return existsDef.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).deriveRightViaEquivalence(assumptions)
    
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        from theorems import existsInBool
        from proveit.common import xEtc        
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        return existsInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}, assumptions)

