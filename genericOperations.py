from proveItCore import *
import collections

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, [A, B])
        self.leftOperand = A
        self.rightOperand = B
        
    def formatted(self, formatType, fenced=False, subLeftFenced=True, subRightFenced=True):
        # override this default as desired
        outStr = ''
        formattedLeft = self.operands[0].formatted(formatType, fenced=subLeftFenced)
        formattedRight = self.operands[1].formatted(formatType, fenced=subRightFenced)
        if formatType == STRING:
            if fenced: outStr += '('
            outStr += formattedLeft + ' ' + self.formattedOperator(formatType) + ' ' + formattedRight
            if fenced: outStr += ')'
        elif formatType == MATHML:
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow>' + formattedLeft
            outStr += self.formattedOperator(formatType)
            outStr += formattedRight + '</mrow>'            
            if fenced: outStr += '</mfenced>'
        return outStr

class AssociativeBinaryOperation(BinaryOperation):
    def __init__(self, operator, operandsOrA, B=None):
        '''
        Expand 2 or more operands to a nested binary operation form.
        '''
        if B:
            A = operandsOrA
            BinaryOperation.__init__(self, operator, A, B)
            self.isNested = False
        else:
            operands = operandsOrA
            assert len(operands) >= 2
            if len(operands) == 2:
                BinaryOperation.__init__(self, operator, operands[0], operands[1])
                self.isNested = False
            else:
                nested = self.remake(operator, operands[1:])
                BinaryOperation.__init__(self, operator, operands[0], nested)
                self.isNested = True
    
    def remake(self, operator, operands):
        return AssociativeBinaryOperation(operator, operands)        
    
    def formatted(self, formatType, fenced=False):
        if self.isNested:
            # No need for parentheses where the associative binary operation is nested
            return BinaryOperation.formatted(self, formatType, fenced, subRightFenced=False)
        else:
            return BinaryOperation.formatted(self, formatType, fenced)                

class NestableOperationOverInstances(OperationOverInstances):
    def __init__(self, operator, constructor, instanceVars=None, instanceExpression=None, conditions=tuple(), nonCondition=None):
        '''
        Nest OperationOverInstances' of the given operator with the given instanceExpression
        for each given instance variable in instanceVars.  Conditions will enter as soon as all 
        of the applicable instance variables have been introduced.
        '''
        from booleans import And
        # pop off the first instance variable
        instanceVar = instanceVars.pop(0)
        if len(instanceVars) == 0:
            # No nesting needed.
            if conditions == None or len(conditions) == 0:
                # no condition
                OperationOverInstances.__init__(self, operator, instanceVar, instanceExpression, nonCondition)
            elif len(conditions) == 1:
                # one condition
                OperationOverInstances.__init__(self, operator, instanceVar, instanceExpression, conditions[0])
            else:
                # multiple conditions
                OperationOverInstances.__init__(self, operator, instanceVar, instanceExpression, And(conditions))                
        else:
            # Do nesting.
            # Find the conditions that are applicable now without need of remaining instance variables
            # versus those that remain.
            applicableConditions = []
            remainingConditions = []
            remainingInstanceVars = set(instanceVars)
            for condition in conditions:
                if len(condition.freeVars() & remainingInstanceVars) == 0:
                    applicableConditions.append(condition) # this conditions is applicable
                else:
                    remainingConditions.append(condition) # this condition is not applicable yet
            # build the applicable condition from applicableConditions
            if len(applicableConditions) == 0:
                applicableCondition = nonCondition # no applicable condition
            elif len(applicableConditions) == 1:
                applicableCondition = applicableConditions[0] # 1 applicable condition
            else:
                applicableCondition = And(applicableConditions) # multiple applicable conditions
            # initialize
            OperationOverInstances.__init__(self, operator, instanceVar, constructor(instanceVars, instanceExpression, remainingConditions), applicableCondition)
