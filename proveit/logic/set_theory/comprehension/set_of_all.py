from proveit import Literal, OperationOverInstances, Operation, Etcetera, safeDefaultOrDummyVar, USE_DEFAULTS
from proveit.common import x, y, f, P, Q, Qmulti, S, yMulti, yEtc

SET = Literal(__package__, 'SET')

class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, domain, conditions=tuple()):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar \in S}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, domain, conditions)
        self.instanceElement = instanceElement

    @classmethod
    def operatorOfOperation(subClass):
        return SET
    
    @staticmethod
    def extractParameters(operands):
        '''
        Extract the parameters from the OperationOverInstances operands:
        instanceVars, instanceElement, conditions, domain
        '''
        params = OperationOverInstances.extractParameters(operands)
        params['instanceElement'] = params['instanceExpr']
        params.pop('instanceExpr')
        return params
        
    def _formatted(self, formatType, fence=False):
        outStr = ''
        innerFence = (len(self.conditions) > 0)
        formattedInstanceVars = ', '.join([var.formatted(formatType) for var in self.instanceVars])
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
    
    def unfoldElemInSet(self, element, assumptions=USE_DEFAULTS):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from _theorems_ import unfoldComprehension, unfoldBasicComprehension, unfoldBasic1CondComprehension, inSupersetIfInComprehension
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0]:
            inSupersetIfInComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions) # x in S side-effect
            if len(self.conditions) == 1:
                Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions[0]
                return unfoldBasic1CondComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element},  {y:self.instanceVars[0]}, assumptions=assumptions)
            else:
                return unfoldBasicComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return unfoldComprehension.specialize({S:self.domain,  Q_op:Q_op_sub, f_op:f_sub, x:element}, {yMulti:self.instanceVars}).deriveConclusion(assumptions)
    
    def deduceElemInSet(self, element, assumptions=USE_DEFAULTS):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        from _theorems_ import foldComprehension, foldBasicComprehension
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return foldBasicComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return foldComprehension.specialize({S:self.domain, Q_op:Q_op_sub, f_op:f_sub, x:element}, {yMulti:self.instanceVars}).deriveConclusion(assumptions)
