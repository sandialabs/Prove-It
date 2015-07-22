from proveit.expression import Operation, Lambda, STRING, LATEX
from proveit.multiExpression import multiExpression
from proveit.everythingLiteral import EVERYTHING
from variables import X

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, (A, B))
        self.leftOperand = A
        self.rightOperand = B
        
    def formatted(self, formatType, fence=False, subLeftFence=True, subRightFence=True):
        # override this default as desired
        formattedLeft = self.leftOperand.formatted(formatType, fence=subLeftFence)
        formattedRight = self.rightOperand.formatted(formatType, fence=subRightFence)
        formattedOp = self.operator.formatted(formatType)
        innerStr = formattedLeft + ' ' + formattedOp + ' ' + formattedRight
        if fence:
            if formatType == LATEX:
                return r'\left(' + innerStr + r'\right)'
            else:
                return '(' + innerStr + ')'
        else: return innerStr

class AssociativeOperation(Operation):
    def __init__(self, operator, *operands):
        '''
        Represent an associative operator operating on any number of operands.
        '''
        Operation.__init__(self, operator, operands)   
        # What is the sound of one (or no) hand clapping?  Who really cares?
        if len(self.operands) < 2:
            raise ValueError("An AssociativeOperation must have at least 2 operands")  
    
    def formatted(self, formatType, fence=False, subFence=True):
        '''
        Format the associative operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        '''
        outStr = ''
        formattedOperands = [operand.formatted(formatType, fence=subFence) for operand in self.operands]
        if formatType == STRING:
            if fence: outStr += '('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += ')'
        elif formatType == LATEX:
            if fence: outStr += r'\left('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += r'\right)'
        return outStr           

class OperationOverInstances(Operation):
    def __init__(self, operator, instanceVars, instanceExpr, domain=EVERYTHING, conditions=tuple()):
        '''
        Create an Operation for the given operator over instances of the given instance Variables,
        instanceVars, for the given instance Expression, instanceExpr under the given conditions
        and/or with instance variables restricted to the given domain.
        That is, the operation operates over all possibilities of given Variable(s) wherever
        the condition(s) is/are satisfied.  Examples include forall, exists, summation, etc.
        instanceVars and conditions may be singular or plural (iterable).
        Internally, this is represented as an Operation whose etcExpr is in the following form
        (where '->' represents a Lambda and {...} represents an ExpressionDict):
          {'instance_mapping' : instanceVars -> {'expression':instanceExpr, 'conditions':conditions}, 'domain':domain}
        '''
        Operation.__init__(self, operator, OperationOverInstances._createOperand(instanceVars, instanceExpr, domain, conditions))
        params = OperationOverInstances.extractParameters(self.operands)
        self.instanceVars = params['instanceVars']
        self.instanceExpr = params['instanceExpr']
        self.domain = params['domain']
        self.conditions = params['conditions']
    
    @staticmethod
    def _createOperand(instanceVars, instanceExpr, domain, conditions):
        lambdaFn = Lambda(instanceVars, {'instance_expression':instanceExpr, 'conditions':multiExpression(conditions)})
        return {'instance_mapping':lambdaFn, 'domain':domain}
    
    @staticmethod
    def extractParameters(operands):
        '''
        Extract the parameters from the OperationOverInstances operands:
        instanceVars, instanceExpr, conditions, domain
        '''
        domain = operands['domain']
        lambdaFn = operands['instance_mapping']
        instanceVars = lambdaFn.arguments
        conditions = lambdaFn.expression['conditions']
        instanceExpr = lambdaFn.expression['instance_expression']
        return {'instanceVars':instanceVars, 'instanceExpr':instanceExpr, 'domain':domain, 'conditions':conditions}
        
    def implicitInstanceVars(self, formatType, overriddenImplicitVars = None):
        '''
        Return instance variables that need not be shown explicitly in the
        list of instance variables in the formatting.
        Use overriddenImplicitVars to declare extra implicit instance variables
        (all or just the overridden ones).
        '''
        return set() if overriddenImplicitVars is None else overriddenImplicitVars

    def implicitConditions(self, formatType):
        '''
        Returns conditions that need not be shown explicitly in the formatting.
        By default, this is empty (all conditions are shown).
        '''
        return set()

    def hasDomain(self):
        '''
        Returns True if this OperationOverInstances has a domain restriction.
        '''
        return self.domain != EVERYTHING
        
    def hasCondition(self):
        '''
        Returns True if this OperationOverInstances has conditions.
        '''
        return self.conditions is not None and len(self.conditions) > 0

    def formatted(self, formatType, fence=False):
        # override this default as desired
        implicitIvars = self.implicitInstanceVars(formatType)
        hasExplicitIvars = (len(implicitIvars) < len(self.instanceVars))
        implicitConditions = self.implicitConditions(formatType)
        hasExplicitConditions = self.hasCondition() and (len(implicitConditions) < len(self.conditions))
        outStr = ''        
        if formatType == STRING :
            if fence: outStr += '['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars:
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
            if self.hasDomain():
                outStr += ' in ' if formatType == STRING else ' \in '
                outStr += self.domain.formatted(formatType)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += ']'
        if formatType == LATEX:
            if fence: outStr += r'\left['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars:
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
            if self.hasDomain():
                outStr += ' in ' if formatType == STRING else ' \in '
                outStr += self.domain.formatted(formatType)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += r'\right]'

        return outStr        

    """
    #    OUT OF DATA
    
    def instanceSubstitution(self, equivalenceForallInstances):
        '''
        Equate this OperationOverInstances, O(x -> f(x) | Q(x)),
        with one that substitutes instance expressions
        given some equivalenceForallInstances = forall_{x | Q(x)} f(x) = g(x).
        Derive and return this equality assuming equivalenceForallInstances.
        Works also when there is no Q(x) condition.
        '''
        from proveit.basiclogic import Forall, Equals
        assert isinstance(equivalenceForallInstances, Forall), "equivalenceForallInstances must be a forall expression: " + str(equivalenceForallInstances)
        equatedMaps = equivalenceForallInstances.equateMaps()
        assert isinstance(equatedMaps, Equals), "Equated maps expected to be equals expression"
        assert self.etcExpr == equatedMaps.lhs or self.etcExpr == equatedMaps.rhs, "Instance substitution expecting equated map involving this OperationOverInstances etcExpr"
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
        from proveit.basiclogic import Forall, Equals
        assert isinstance(equivalenceForallInstances, Forall), "equivalenceForallInstances must be a forall expression"
        equatedMaps = equivalenceForallInstances.equateMaps()
        assert isinstance(equatedMaps, Equals), "Equated maps expected to be equals expression"
        assert self.etcExpr == equatedMaps.lhs or self.etcExpr == equatedMaps.rhs, "Instance substitution expecting equated map involving this OperationOverInstances etcExpr"
        if self.etcExpr == equatedMaps.lhs:
            return equatedMaps.rhsSubstitute(X, Operation(self.operator, [X]))
        else:
            return equatedMaps.lhsSubstitute(X, Operation(self.operator, [X]))
    """