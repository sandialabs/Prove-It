from proveit import Operation, Etcetera, MultiVariable, Lambda, compositeExpression, NamedExpressions

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
        (where '->' represents a Lambda and the list of tuples are NambedExpressions:
        [('imap', instanceVars -> [('iexpr',instanceExpr), ('conditions',conditions)]), ('domain',domain)]
        '''
        Operation.__init__(self, operator, OperationOverInstances._createOperand(instanceVars, instanceExpr, domain, conditions))
        params = OperationOverInstances.extractParameters(self.operands)
        self.instanceVars = params['instanceVars']
        self.instanceExpr = params['instanceExpr']
        self.domain = params['domain']
        self.conditions = params['conditions']
    
    @staticmethod
    def _createOperand(instanceVars, instanceExpr, domain, conditions):
        lambdaFn = Lambda(instanceVars, NamedExpressions([('iexpr',instanceExpr), ('conds',compositeExpression(conditions))]))
        if domain is None:
            return NamedExpressions([('imap',lambdaFn)])
        else:
            return NamedExpressions([('imap',lambdaFn), ('domain',domain)])
    
    @staticmethod
    def extractParameters(operands):
        '''
        Extract the parameters from the OperationOverInstances operands:
        instanceVars, instanceExpr, conditions, domain
        '''
        domain = operands['domain'] if 'domain' in operands else None
        instanceMapping = operands['imap'] # instance mapping
        instanceVars = instanceMapping.parameters
        conditions = instanceMapping.body['conds']
        instanceExpr = instanceMapping.body['iexpr'] # instance expression
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
        return len(self.conditions) > 0

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
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)

    def _formatted(self, formatType, fence=False):
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
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
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
                outStr += ', '.join([var.formatted(formatType) for var in self.instanceVars if var not in implicitIvars])
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