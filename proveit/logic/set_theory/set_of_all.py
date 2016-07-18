from proveit import Literal, OperationOverInstances, Operation, Etcetera, MultiVariable
from proveit.common import x, y, f, P, Q, yEtc

SET = Literal(__package__, 'SET')

class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, domain=None, conditions=tuple()):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, domain, conditions)
        self.instanceElement = instanceElement

    @classmethod
    def operatorOfOperation(subClass):
        return SET
    
    def formatted(self, formatType, fence=False):
        outStr = ''
        innerFence = (len(self.conditions) > 0)
        formattedInstanceVars = self.instanceVars.formatted(formatType, fence=False)
        formattedInstanceElement = self.instanceElement.formatted(formatType, fence=innerFence)
        formattedDomain = self.domain.formatted(formatType, fence=True)
        formattedConditions = self.conditions.formatted(formatType, fence=False) 
        if formatType == 'latex': outStr += r"\left\{"
        else: outStr += "{"
        outStr += formattedInstanceElement
        if len(self.conditions) > 0:
            if formatType == 'latex': outStr += r'~|~'
            else: outStr += ' s.t. ' # such that
            outStr += formattedConditions
        if formatType == 'latex': outStr += r"\right\}"
        else: outStr += "}"
        outStr += '_{' + formattedInstanceVars
        if self.domain is not None:
            if formatType == 'latex': outStr += r' \in '
            else: outStr += ' in '
            outStr += formattedDomain
        outStr += '}'
        return outStr

    def unfoldElemInSet(self, element):
        '''
        From (x in {Q(y) | P(y)}), derive and return P(x), where x is meant as the given element.
        '''
        from theorems import unfoldSetOfAll, unfoldSimpleSetOfAll
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return unfoldSimpleSetOfAll.specialize({Pop:Psub, x:element, y:self.instanceVars[0]}).deriveConclusion()
        else:
            Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return unfoldSetOfAll.specialize({f_op:f_sub, Q_op:Q_op_sub, x:element, yEtc:self.instanceVars}).deriveConclusion()
    
    def deduceElemInSet(self, element):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        from theorems import foldSetOfAll, foldSimpleSetOfAll
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return foldSimpleSetOfAll.specialize({Pop:Psub, x:element, y:self.instanceVars[0]}).deriveConclusion()
        else:
            Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return foldSetOfAll.specialize({f_op:f_sub, Q_op:Q_op_sub, x:element, yEtc:self.instanceVars}).deriveConclusion()
