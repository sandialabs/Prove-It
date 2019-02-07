from proveit import Literal, OperationOverInstances, Operation, ExprList, USE_DEFAULTS
from proveit._common_ import x, y, f, P, Q, QQ, S, yy

class SetOfAll(OperationOverInstances):
    # operator of the SetOfAll operation
    _operator_ = Literal(stringFormat='Set', context=__file__)    
    
    def __init__(self, instanceVar, instanceElement, domain, conditions=tuple()):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar \in S}
        '''
        OperationOverInstances.__init__(self, SetOfAll._operator_, instanceVar, instanceElement, domain=domain, conditions=conditions)
        self.instanceElement = self.instanceExpr

    @staticmethod
    def extractInitArgValue(argName, operators, operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        '''
        from proveit.logic import InSet
        if argName=='instanceElement':
            return operands.body # instance mapping
        elif argName=='instanceVar':
            return operands.parameter
        elif argName=='domain':
            # the first condition must be the domain condition
            domainCondition = operands.conditions[0]
            assert isinstance(domainCondition, InSet), "Expecting the first condition of a SetOfAll object to be the domain condition of type InSet"
            assert domainCondition.element==operands.parameter, "Expecting the first condition of a SetOfAll object to be the domain condition with the proper element"
            return domainCondition.domain
        elif argName=='conditions':
            return ExprList(*operands.conditions[1:]) # all except the domain condition
        else:
            return OperationOverInstances.extractInitArgValue(argName, operators, operands)
        
    def _formatted(self, formatType, fence=False, **kwargs):
        outStr = ''
        explicit_conditions = self.explicitConditions()
        inner_fence = (len(explicit_conditions) > 0)
        formatted_instance_vars = ', '.join([var.formatted(formatType) for var in self.instanceVars])
        formatted_instance_element = self.instanceElement.formatted(formatType, fence=inner_fence)
        formatted_domain = self.domain.formatted(formatType, fence=True)
        if formatType == 'latex': outStr += r"\left\{"
        else: outStr += "{"
        outStr += formatted_instance_element
        if len(explicit_conditions) > 0:
            formatted_conditions = explicit_conditions.formatted(formatType, fence=False) 
            if formatType == 'latex': outStr += r'~|~'
            else: outStr += ' s.t. ' # such that
            outStr += formatted_conditions
        if formatType == 'latex': outStr += r"\right\}"
        else: outStr += "}"
        outStr += '_{' + formatted_instance_vars
        if self.domain is not None:
            if formatType == 'latex': outStr += r' \in '
            else: outStr += ' in '
            outStr += formatted_domain
        outStr += '}'
        return outStr
    
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from ._theorems_ import unfoldComprehension, unfoldBasicComprehension, unfoldBasic1CondComprehension, inSupersetIfInComprehension
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
    
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        from ._theorems_ import foldComprehension, foldBasicComprehension
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return foldBasicComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return foldComprehension.specialize({S:self.domain, Q_op:Q_op_sub, f_op:f_sub, x:element}, {yMulti:self.instanceVars}).deriveConclusion(assumptions)
