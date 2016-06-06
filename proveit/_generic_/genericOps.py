from proveit import Operation, Lambda, compositeExpression, MultiVariable, ExpressionList, Etcetera

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, (A, B))
        self.leftOperand = A
        self.rightOperand = B    

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=False, subLeftFence=True, subRightFence=True):
        # override this default as desired
        formattedLeft = self.leftOperand.formatted(formatType, fence=subLeftFence)
        formattedRight = self.rightOperand.formatted(formatType, fence=subRightFence)
        formattedOp = self.operator.formatted(formatType)
        innerStr = formattedLeft + ' ' + formattedOp + ' ' + formattedRight
        if fence:
            if formatType == 'latex':
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
        assert isinstance(self.operands, ExpressionList)
        # What is the sound of one (or no) hand clapping?  Who really cares?
        if len(self.operands) < 2:
            # A single Etcetera operand is okay though (it will have to be replace with
            # 2 or more items)
            if len(self.operands) == 0 or not isinstance(self.operands[0], Etcetera):
                raise ValueError("An AssociativeOperation must have at least 2 operands")  
    
    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
    
    def formatted(self, formatType, fence=False, subFence=True):
        '''
        Format the associative operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        '''
        formattedOperator = self.operator.formatted(formatType) 
        return self.operands.formatted(formatType, fence=fence, subFence=subFence, formattedOperator=formattedOperator)
        """
        outStr = ''
        # insert ellipses (two dots in our case) before and after Etcetera expressions
        formattedOperands = [] 
        for operand in self.operands:
            if isinstance(operand, Etcetera):
                if len(formattedOperands) > 0 and formattedOperands[-1] == '..' + spc:
                    # instead of having "..  .." back-to-back, do ".."
                    formattedOperands[-1] = '...'
                else:
                    formattedOperands.append(spc + '..')
                formattedOperands.append(operand.bundledExpr.formatted(formatType, fence=subFence))
                formattedOperands.append('..' + spc)
            else:
                formattedOperands.append(operand.formatted(formatType, fence=subFence))
        # put the formatted operator between each of formattedOperands
        if formatType == STRING:
            if fence: outStr += '('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += ')'
        elif formatType == LATEX:
            if fence: outStr += r'\left('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += r'\right)'
        return outStr           
        """

class OperationOverInstances(Operation):
    def __init__(self, operator, instanceVars, instanceExpr, domain=None, conditions=tuple()):
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
        lambdaFn = Lambda(instanceVars, {'instance_expression':instanceExpr, 'conditions':compositeExpression(conditions)})
        if domain is not None:
            return {'instance_mapping':lambdaFn, 'domain':domain}
        else:
            return {'instance_mapping':lambdaFn}
    
    @staticmethod
    def extractParameters(operands):
        '''
        Extract the parameters from the OperationOverInstances operands:
        instanceVars, instanceExpr, conditions, domain
        '''
        domain = operands['domain'] if 'domain' in operands else None
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
        return self.domain is not None
        
    def hasCondition(self):
        '''
        Returns True if this OperationOverInstances has conditions.
        '''
        return self.conditions is not None and len(self.conditions) > 0

    @classmethod
    def make(operationClass, coreInfo, subExpressions):
        '''
        Make the appropriate OperationOverInstances.  coreInfo should equal ['Operation'].
        The first of the subExpressions should be the operator and the subsequent ones 
        should be operands.  For OperationOverInstances sub-classes that use a specific Literal 
        operator, override 'operatorOfOperation' and the default behavior of 'make' will be to 
        instantiate the OperationOverInstances sub-class with extracted parameters of the operand:
        'instanceVars', 'instanceExpr', 'domain', 'conditions'.  Override extractParameters if
        parameters are renamed.
        '''
        if len(coreInfo) != 1 or coreInfo[0] != 'Operation':
            raise ValueError("Expecting Operation coreInfo to contain exactly one item: 'Operation'")
        if len(subExpressions) != 2:
            raise ValueError('Expecting exactly two subExpressions for an OperationOverInstances')
        operator, operands = subExpressions[0], subExpressions[1]
        subClassOperator = operationClass.operatorOfOperation()
        if subClassOperator != operator:
            raise ValueError('Unexpected operator, ' + str(operator) + ', when making ' + str(operationClass)) 
        return operationClass(**operationClass.extractParameters(operands))
    
    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, formatType, fence=False):
        # override this default as desired
        implicitIvars = self.implicitInstanceVars(formatType)
        hasExplicitIvars = (len(implicitIvars) < len(self.instanceVars))
        implicitConditions = self.implicitConditions(formatType)
        hasExplicitConditions = self.hasCondition() and (len(implicitConditions) < len(self.conditions))
        outStr = ''        
        if formatType == 'string':
            if fence: outStr += '['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars:
                outStr += self.instanceVars.formatted(formatType, fence=False)
                #outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
            if self.hasDomain():
                outStr += ' in ' if formatType == 'string' else ' \in '
                outStr += self.domain.formatted(formatType, fence=True)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += self.conditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += ']'
        if formatType == 'latex':
            if fence: outStr += r'\left['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars:
                outStr += self.instanceVars.formatted(formatType, fence=False)
                #outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
            if self.hasDomain():
                outStr += ' in ' if formatType == 'string' else ' \in '
                outStr += self.domain.formatted(formatType, fence=True)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += "~|~"
                outStr += self.conditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += r'\right]'

        return outStr        

    def instanceSubstitution(self, equivalenceForallInstances):
        '''
        Equate this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..),
        with one that substitutes instance expressions given some 
        equivalenceForallInstances = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Derive and return the following type of equality assuming equivalenceForallInstances:
        Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..) = Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        from proveit.logic.axioms import instanceSubstitution
        from proveit.logic import Forall, Equals
        from proveit.number import num
        from proveit.common import n, Q, Qetc, xEtc, yEtc, zEtc, etc_QxEtc, f, g, fxEtc, fyEtc, gxEtc, gzEtc, Upsilon, S
        if not isinstance(equivalenceForallInstances, Forall):
            raise InstanceSubstitutionException("equivalenceForallInstances must be a forall expression", self, equivalenceForallInstances)
        if len(equivalenceForallInstances.instanceVars) != len(self.instanceVars):
            raise InstanceSubstitutionException("equivalenceForallInstances must have the same number of variables as the OperationOverInstances having instances substituted", self, equivalenceForallInstances)
        if equivalenceForallInstances.domain != self.domain:
            raise InstanceSubstitutionException("equivalenceForallInstances must have the same domain as the OperationOverInstances having instances substituted", self, equivalenceForallInstances)
        # map from the forall instance variables to self's instance variables
        iVarSubstitutions = {forallIvar:selfIvar for forallIvar, selfIvar in zip(equivalenceForallInstances.instanceVars, self.instanceVars)}
        if equivalenceForallInstances.conditions.substituted(iVarSubstitutions) != self.conditions:
            raise InstanceSubstitutionException("equivalenceForallInstances must have the same conditions as the OperationOverInstances having instances substituted", self, equivalenceForallInstances)
        if not isinstance(equivalenceForallInstances.instanceExpr, Equals):
            raise InstanceSubstitutionException("equivalenceForallInstances be an equivalence within Forall: " + str(equivalenceForallInstances))
        if equivalenceForallInstances.instanceExpr.lhs.substituted(iVarSubstitutions) != self.instanceExpr:
            raise InstanceSubstitutionException("lhs of equivalence in equivalenceForallInstances must match the instance expression of the OperationOverInstances having instances substituted", self, equivalenceForallInstances)
        f_op, f_op_sub = Operation(f, self.instanceVars), self.instanceExpr
        g_op, g_op_sub = Operation(g, self.instanceVars), equivalenceForallInstances.instanceExpr.rhs.substituted(iVarSubstitutions)
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        return instanceSubstitution.specialize({Upsilon:self.operator, xEtc:self.instanceVars, yEtc:self.instanceVars, zEtc:self.instanceVars, \
                                                Q_op:Q_op_sub, S:self.domain, f_op:f_op_sub, g_op:g_op_sub}).deriveConclusion()

    def substituteInstances(self, equivalenceForallInstances):
        '''
        Assuming this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..)
        to be a true statement, derive and return Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        given some equivalenceForallInstances = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        substitution = self.instanceSubstitution(equivalenceForallInstances)
        return substitution.deriveRightViaEquivalence()
        
class InstanceSubstitutionException(Exception):
    def __init__(self, msg, operationOverInstances, equivalenceForallInstances):
        self.msg = msg
        self.operationOverInstances = operationOverInstances
        self.equivalenceForallInstances = equivalenceForallInstances
    def __str__(self):
        return self.msg + '.\n  operationOverInstances: ' + str(self.operationOverInstances) + '\n  equivalenceForallInstances: ' + str(self.equivalenceForallInstances)