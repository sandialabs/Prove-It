from proveit._core_.expression import Expression
from proveit._core_.expression.lambda_expr import Lambda
from proveit._core_.expression.composite import ExprList, singleOrCompositeExpression, compositeExpression, Composite, NamedExprs
from proveit._core_.defaults import USE_DEFAULTS
from .operation import Operation

class OperationOverInstances(Operation):
    def __init__(self, operator, instanceVarOrVars, instanceExpr, domain=None, domains=None, conditions=tuple(), styles=dict()):
        '''
        Create an Operation for the given operator that is applied over instances of the 
        given instance Variables, instanceVars, for the given instance Expression, instanceExpr
        under the given conditions.  
        That is, the operation operates over all possibilities of given Variable(s) wherever
        the condition(s) is/are satisfied.  Examples include forall, exists, summation, etc.
        instanceVars and conditions may be singular or finstanceVarOrVarsplural (iterable).
              
        If a domain is supplied, additional conditions are generated that each instance 
        Variable is in the domain "set": InSet(x_i, domain), where x_i is for each instance 
        variable.  If, instead, domains are supplied, then each instance variable is supplied
        with its own domain (one for each instance variable).  Internally, this is represented
        as an Operation with a single Lambda expression operand that maps the instance variables 
        to a NamedExpression in the following form:
            instanceVars -> [('iexpr',instanceExpr), ('conditions',conditions)]
        
        The set of "domain" conditions come at the beginning of this conditions list and
        can be accessed via the 'implicitConditions' attribute, and the 'domain' or 'domains'
        can be accessed via attributes of the same name.  Whether the OperationOverInstances
        is constructed with domain/domains explicitly, or they are provided at the beginning
        of the conditions list (in the proper order) does not matter.  Essentially, the 
        'domain' concept is simply a convenience for conditions of this form and may be 
        formatted using a shorthand notation.  For example, "forall_{x in S | Q(x)} P(x)" 
        is a shorthand notation for "forall_{x | x in S, Q(x)} P(x)".  The non-domain-conditions 
        are accessible via the 'explicitConditions' attribute.  The 'conditions' attribute has the 
        full proper list of conditions.
        '''
        from proveit.logic import InSet
        instanceVars = compositeExpression(instanceVarOrVars)
        if domain is not None:
            # prepend domain conditions
            if domains is not None:
                raise ValueError("Provide a single domain or multiple domains, not both")
            if not isinstance(domain, Expression):
                raise TypeError("The domain should be an 'Expression' type")
            domains = [domain]*len(instanceVars)
        if domains is not None: 
            # prepend domain conditions
            if len(domains) != len(instanceVars):
                raise ValueError("When specifying multiple domains, the number should be the same as the number of instance variables.")         
            conditions = [InSet(instanceVar, domain) for instanceVar, domain in zip(instanceVars, domains)] + list(conditions)
        conditions = compositeExpression(conditions)
        Operation.__init__(self, operator, OperationOverInstances._createOperand(instanceVars, instanceExpr, conditions), styles=styles)
        self.instanceVars = instanceVars
        if len(self.instanceVars) == 1:
            self.instanceVar = self.instanceVars[0]
        self.instanceExpr = instanceExpr
        self.conditions = conditions

        # extract the domain or domains from the condition (regardless of whether the domain/domains was explicitly provided
        # or implicit through the conditions).
        if len(conditions) >= len(instanceVars):
            domains = []
            for instanceVar, condition in zip(instanceVars, conditions):
                if isinstance(condition, InSet) and condition.element == instanceVar:
                    domains.append(condition.domain)
            if len(domains) == len(instanceVars):
                # There is a domain condition for each instance variable.
                if all(domain==domains[0] for domain in domains):
                    self.domain_or_domains = self.domain = domains[0] # all the same domain
                else:
                    self.domain_or_domains = self.domains = ExprList(*domains)
                        
    @staticmethod
    def _createOperand(instanceVars, instanceExpr, conditions):
        return Lambda(instanceVars, NamedExprs([('iexpr',instanceExpr), ('conds',conditions)]))
    
    @staticmethod
    def extractInitArgValue(argName, operator, operand):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value as determined by the
        given operator and operand for an OperationOverInstances
        Expression.
        
        Override this if the __init__ argument names are different than the
        default.
        '''
        if argName=='operator':
            return operator
        if argName=='domain' or argName=='domains': 
            return None # specify domains implicitly through conditions
        if argName=='instanceVarOrVars':
            return singleOrCompositeExpression(operand.parameters)
        elif argName=='instanceExpr':
            return operand.body['iexpr'] 
        elif argName=='conditions':
            conditions = operand.body['conds']
            #if len(conditions)==0: return tuple()
            return conditions
    
    def explicitInstanceVars(self):
        '''
        Return the instance variables that are to be shown explicitly 
        in the formatting  (as opposed to being made implicit via conditions).  
        By default, this is all of the instance variables.  May be overridden
        for different behavior however.
        '''
        return self.instanceVars

    def hasDomain(self):
        '''
        Returns True if this OperationOverInstances has a single domain restriction(s).
        '''
        return hasattr(self, 'domain')

    def hasDomains(self):
        '''
        Returns True if this OperationOverInstances has multiple domain restriction(s).
        '''
        return hasattr(self, 'domains')
    
    def hasDomainOrDomains(self):
        '''
        Returns True if this OperationOverInstances has one or more domain restriction(s).
        '''        
        return self.hasDomain() or self.hasDomains()    
    
    def explicitConditions(self):
        '''
        Return the conditions that are to be show explicitly in the formatting
        (after the "such that" symbol "|").  By default, this includes all of
        the conditions except implicit "domain" conditions.
        '''
        if self.hasDomainOrDomains():
            # return the conditions after the implicit domain conditions
            return ExprList(*self.conditions.entries[len(self.instanceVars):])
        return self.conditions # no domain conditions, so all of them are explicit
    
    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)

    def _formatted(self, formatType, fence=False):
        # override this default as desired
        explicitIvars = self.explicitInstanceVars() # the instance vars to show explicitly
        explicitConditions = self.explicitConditions() # the conditions to show explicitly after '|'
        hasExplicitIvars = (len(explicitIvars) > 0)
        hasExplicitConditions = (len(explicitConditions) > 0)
        outStr = ''
        formattedVars = ', '.join([var.formatted(formatType, abbrev=True) for var in explicitIvars])
        if formatType == 'string':
            if fence: outStr += '['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars: 
                if self.hasDomains(): outStr += '(' + formattedVars +')'
                else: outStr += formattedVars
            if self.hasDomainOrDomains():
                outStr += ' in '
                outStr += self.domain_or_domains.formatted(formatType, formattedOperator='*', fence=False)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += explicitConditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += ']'
        if formatType == 'latex':
            if fence: outStr += r'\left['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars: 
                if self.hasDomains(): outStr += '(' + formattedVars +')'
                else: outStr += formattedVars
            if self.hasDomainOrDomains():
                outStr += r' \in '
                outStr += self.domain_or_domains.formatted(formatType, formattedOperator=r'\times', fence=False)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += "~|~"
                outStr += explicitConditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + self.instanceExpr.formatted(formatType,fence=True)
            if fence: outStr += r'\right]'

        return outStr
    
    """
    def instanceSubstitution(self, universality, assumptions=USE_DEFAULTS):
        '''
        Equate this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..),
        with one that substitutes instance expressions given some 
        universality = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Derive and return the following type of equality assuming universality:
        Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..) = Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        from proveit.logic.equality._axioms_ import instanceSubstitution, noDomainInstanceSubstitution
        from proveit.logic import Forall, Equals
        from proveit import KnownTruth
        from proveit._common_ import n, Qmulti, xMulti, yMulti, zMulti, f, g, Upsilon, S
        if isinstance(universality, KnownTruth):
            universality = universality.expr
        if not isinstance(universality, Forall):
            raise InstanceSubstitutionException("'universality' must be a forall expression", self, universality)
        if len(universality.instanceVars) != len(self.instanceVars):
            raise InstanceSubstitutionException("'universality' must have the same number of variables as the OperationOverInstances having instances substituted", self, universality)
        if universality.domain != self.domain:
            raise InstanceSubstitutionException("'universality' must have the same domain as the OperationOverInstances having instances substituted", self, universality)
        # map from the forall instance variables to self's instance variables
        iVarSubstitutions = {forallIvar:selfIvar for forallIvar, selfIvar in zip(universality.instanceVars, self.instanceVars)}
        if universality.conditions.substituted(iVarSubstitutions) != self.conditions:
            raise InstanceSubstitutionException("'universality' must have the same conditions as the OperationOverInstances having instances substituted", self, universality)
        if not isinstance(universality.instanceExpr, Equals):
            raise InstanceSubstitutionException("'universality' must be an equivalence within Forall: " + str(universality))
        if universality.instanceExpr.lhs.substituted(iVarSubstitutions) != self.instanceExpr:
            raise InstanceSubstitutionException("lhs of equivalence in 'universality' must match the instance expression of the OperationOverInstances having instances substituted", self, universality)
        f_op, f_op_sub = Operation(f, self.instanceVars), self.instanceExpr
        g_op, g_op_sub = Operation(g, self.instanceVars), universality.instanceExpr.rhs.substituted(iVarSubstitutions)
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if self.hasDomain():
            return instanceSubstitution.specialize({Upsilon:self.operator, Q_op:Q_op_sub, S:self.domain, f_op:f_op_sub, g_op:g_op_sub}, 
                                                    relabelMap={xMulti:universality.instanceVars, yMulti:self.instanceVars, zMulti:self.instanceVars}, assumptions=assumptions).deriveConsequent(assumptions=assumptions)
        else:
            return noDomainInstanceSubstitution.specialize({Upsilon:self.operator, Q_op:Q_op_sub, f_op:f_op_sub, g_op:g_op_sub}, 
                                                             relabelMap={xMulti:universality.instanceVars, yMulti:self.instanceVars, zMulti:self.instanceVars}, assumptions=assumptions).deriveConsequent(assumptions=assumptions)

    def substituteInstances(self, universality, assumptions=USE_DEFAULTS):
        '''
        Assuming this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..)
        to be a true statement, derive and return Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        given some 'universality' = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        substitution = self.instanceSubstitution(universality, assumptions=assumptions)
        return substitution.deriveRightViaEquivalence(assumptions=assumptions)
    """
        
class InstanceSubstitutionException(Exception):
    def __init__(self, msg, operationOverInstances, universality):
        self.msg = msg
        self.operationOverInstances = operationOverInstances
        self.universality = universality
    def __str__(self):
        return self.msg + '.\n  operationOverInstances: ' + str(self.operationOverInstances) + '\n  universality: ' + str(self.universality)