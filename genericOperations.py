from proveItCore import *
import collections

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, (A, B))
        self.leftOperand = A
        self.rightOperand = B
        
    def formatted(self, formatType, fenced=False, subLeftFenced=True, subRightFenced=True):
        # override this default as desired
        outStr = ''
        formattedLeft = self.leftOperand.formatted(formatType, fenced=subLeftFenced)
        formattedRight = self.rightOperand.formatted(formatType, fenced=subRightFenced)
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

class AssociativeOperation(Operation):
    def __init__(self, operator, *operands):
        '''
        Represent an associative operator operating on any number of operands.
        '''
        Operation.__init__(self, operator, operands)   
        # What is the sound of one (or no) hand clapping?  Who really cares?
        if len(self.operand) < 2:
            raise ValueError("An AssociativeOperation must have at least 2 operands")  
        self.operands = self.operand.expressions
    
    def formatted(self, formatType, fenced=False, subFenced=True):
        '''
        Format the associative operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.formattedOperator(formatType).
        '''
        outStr = ''
        formattedOperands = [operand.formatted(formatType, fenced=subFenced) for operand in self.operands]
        if formatType == STRING:
            if fenced: outStr += '('
            outStr += (' ' + self.formattedOperator(formatType) + ' ').join(formattedOperands)
            if fenced: outStr += ')'
        elif formatType == MATHML:
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow>'
            outStr += (' ' + self.formattedOperator(formatType) + ' ').join(formattedOperands)
            outStr += '</mrow>'            
            if fenced: outStr += '</mfenced>'
        return outStr           

class OperationOverInstances(Operation):
    def __init__(self, operator, instanceVars, instanceExpression, conditions=None):
        '''
        Create an Operation for the given operator over instances of the given 
        instanceVar(s) (Variables) for the given instanceExpression under the given conditions.
        That is, the operation operates over all possibilities of given Variable(s) wherever
        the condition is satisfied.  Examples include forall, exists, summation, etc.
        Internally, this is represented as an Operation whose operand is a Lambda function
        (with an optional domain condition).  instanceVars and conditions may be singular or 
        plural (iterable).
        '''
        Operation.__init__(self, operator, Lambda(instanceVars, instanceExpression, conditions))
        lambdaOperand = self.operand
        self.instanceVar = lambdaOperand.argument
        self.instanceExpression = lambdaOperand.expression
        self.condition = lambdaOperand.domainCondition

    def implicitInstanceVar(self):
        '''
        If the conditions are that the instance variables are in some set, then
        the instance variables are implicit (stating conditions indicates
        the instance variable).
        '''
        from sets import In
        if self.condition is None: return False
        inSetElements = {condition.element for condition in self.condition if isinstance(condition, In)}
        return all(var in inSetElements for var in self.instanceVar)
    
    def hasCondition(self):
        '''
        Returns True if this OperationOverInstances has conditions.
        '''
        return len(self.condition) > 0

    def formatted(self, formatType, fenced=False):
        # override this default as desired
        implicitIvar = self.implicitInstanceVar()
        outStr = ''        
        if formatType == STRING:
            if fenced: outStr += '['
            outStr += self.formattedOperator(formatType) + '_{'
            if not implicitIvar:
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVar])
            if self.hasCondition():
                if not implicitIvar: outStr += " | "
                outStr += ', '.join(condition.formatted(formatType) for condition in self.condition) 
            outStr += '} ' + self.instanceExpression.formatted(formatType)
            if fenced: outStr += ']'
        elif formatType == MATHML:        
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow><msub>' + self.formattedOperator(formatType)
            if self.hasCondition(): outStr += '<mrow>'
            if not implicitIvar:
                for var in self.instanceVar: outStr += var.formatted(formatType)
            if self.hasCondition(): 
                if not implicitIvar:
                    outStr += '<mo>|</mo>'
                for condition in self.condition: 
                    outStr += condition.formatted(formatType) 
                outStr += '</mrow>'
            outStr += '</msub>' + self.instanceExpression.formatted(formatType)
        return outStr        

    def instanceSubstitution(self, equivalenceForallInstances):
        '''
        Equate this OperationOverInstances, O(x -> f(x) | Q(x)),
        with one that substitutes instance expressions
        given some equivalenceForallInstances = forall_{x | Q(x)} f(x) = g(x).
        Derive and return this equality assuming equivalenceForallInstances.
        Works also when there is no Q(x) condition.
        '''
        from booleans import Forall, X
        from equality import Equals
        assert isinstance(equivalenceForallInstances, Forall), "equivalenceForallInstances must be a forall expression: " + str(equivalenceForallInstances)
        equatedMaps = equivalenceForallInstances.equateMaps()
        assert isinstance(equatedMaps, Equals), "Equated maps expected to be equals expression"
        assert self.operand == equatedMaps.lhs or self.operand == equatedMaps.rhs, "Instance substitution expecting equated map involving this OperationOverInstances operand"
        equatedOperationOverInstances = equatedMaps.substitution(X, Operation(self.operator, X))
        assert isinstance(equatedOperationOverInstances, Equals), "Equated operation over instance expected to be equals expression"
        if self == equatedOperationOverInstances.rhs:
            equatedOperationOverInstances = equatedOperationOverInstances.deriveReversed()
        assert self == equatedOperationOverInstances.lhs, "Instance substitution expecting equated operation over instances to involve self"
        return equatedOperationOverInstances

    def substituteInstances(self, equivalenceForallInstances):
        '''
        Assuming OperationOverInstances self as O(x -> f(x) | Q(x)), derive and return 
        O(x -> g(x) | Q(x)) given some equivalenceForallInstances = forall_{x | Q(x)} f(x) = g(x).
        Works also when there is no Q(x) condition.
        '''
        from booleans import Forall, X
        from equality import Equals
        assert isinstance(equivalenceForallInstances, Forall), "equivalenceForallInstances must be a forall expression"
        equatedMaps = equivalenceForallInstances.equateMaps()
        assert isinstance(equatedMaps, Equals), "Equated maps expected to be equals expression"
        assert self.operand == equatedMaps.lhs or self.operand == equatedMaps.rhs, "Instance substitution expecting equated map involving this OperationOverInstances operand"
        if self.operand == equatedMaps.lhs:
            return equatedMaps.rhsSubstitute(X, Operation(self.operator, [X]))
        else:
            return equatedMaps.lhsSubstitute(X, Operation(self.operator, [X]))
        