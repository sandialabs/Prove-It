from proveit.statement import *
import collections

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, (A, B))
        assert len(A) == 1 and len(B) == 1, 'Cannot have ExpressionLists in Binary operation because it can lead to ambiguity since ExpressionLists cannot nest.'
        self.leftOperand = A
        self.rightOperand = B
        
    def formatted(self, formatType, fenced=False, subLeftFenced=True, subRightFenced=True):
        # override this default as desired
        outStr = ''
        formattedLeft = self.leftOperand.formatted(formatType, fenced=subLeftFenced)
        formattedRight = self.rightOperand.formatted(formatType, fenced=subRightFenced)
        formattedOp = self.formattedOperator(formatType)
        assert not formattedOp is None, 'formattedOperator needs to be implemented for ' + str(self.__class__)
        if formatType == STRING or formatType == LATEX:
            if fenced: outStr += '('
            outStr += formattedLeft + ' ' + formattedOp + ' ' + formattedRight
            if fenced: outStr += ')'
        elif formatType == MATHML:
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow>' + formattedLeft
            outStr += formattedOp
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
        if formatType == STRING or formatType == LATEX:
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

    def implicitInstanceVars(self, formatType, overriddenImplicitVars = None):
        '''
        Return instance variables that need not be shown explicitly in the
        list of instance variables in the formatting.  By default,
        this will be all instance variables if all instance variables 
        have conditions of being in sets, or none of them (all or nothing).
        Use overriddenImplicitVars to declare extra implicit instance variables
        (all or just the overridden ones).
        '''
        from sets import In
        if self.condition is None: return False
        inSetElements = {condition.element for condition in self.condition if isinstance(condition, In)}
        if overriddenImplicitVars is None: overriddenImplicitVars = set()
        inSetVars = {var for var in self.instanceVar if var in inSetElements or var in overriddenImplicitVars}
        if len(inSetVars) == len(self.instanceVar):
            return inSetVars # all
        else:
            return overriddenImplicitVars # or nothing / overriddens

    def implicitConditions(self, formatType):
        '''
        Returns conditions that need not be shown explicitly in the formatting.
        By default, this is empty (all conditions are shown).
        '''
        return set()
    
    def hasCondition(self):
        '''
        Returns True if this OperationOverInstances has conditions.
        '''
        return len(self.condition) > 0

    def formatted(self, formatType, fenced=False):
        # override this default as desired
        implicitIvars = self.implicitInstanceVars(formatType)
        hasExplicitIvars = (len(implicitIvars) < len(self.instanceVar))
        implicitConditions = self.implicitConditions(formatType)
        hasExplicitConditions = self.hasCondition() and (len(implicitConditions) < len(self.condition))
        outStr = ''        
        if formatType == STRING or formatType == LATEX:
            if fenced: outStr += '['
            outStr += self.formattedOperator(formatType) + '_{'
            if hasExplicitIvars:
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVar if var not in implicitIvars])
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += ', '.join(condition.formatted(formatType) for condition in self.condition if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpression.formatted(formatType)
            if fenced: outStr += ']'
        elif formatType == MATHML:        
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow><msub>' + self.formattedOperator(formatType)
            outStr += '<mrow><mfenced open="" close="">'
            if hasExplicitIvars:
                for var in self.instanceVar: 
                    if var not in implicitIvars: outStr += var.formatted(formatType)
            if hasExplicitConditions: 
                if hasExplicitIvars:
                    outStr += '</mfenced><mo>&#x2223;</mo><mfenced open="" close="">'
                for condition in self.condition: 
                    if condition not in implicitConditions: outStr += condition.formatted(formatType) 
            outStr += '</mfenced></mrow>'
            outStr += '</msub>' + self.instanceExpression.formatted(formatType)
            if fenced: outStr += '</mfenced>'
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
        