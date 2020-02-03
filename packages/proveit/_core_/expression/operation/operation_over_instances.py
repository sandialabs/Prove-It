from proveit._core_.expression import Expression
from proveit._core_.expression.lambda_expr import Lambda
from proveit._core_.expression.composite import ExprTuple, singleOrCompositeExpression, compositeExpression
from .operation import Operation

class OperationOverInstances(Operation):
    '''
    OperationOverInstances description: TODO
    '''
    
    '''
    When deriving from OperationOverInstances, set the '_init_argname_mapping' 
    static variable to indicate how the initialization argument names in the 
    derived class correspond with the OperationOverInstances argument names.
    Omitted keys will be presumed to be unchanged argument names.  This is
    a simple way to make extractInitArgValue and extractMyInitArgValue function
    properly without overriding them.
    '''
    _init_argname_mapping_ = {'instanceVarOrVars':'instanceVarOrVars', 'instanceExpr':'instanceExpr', 'domain':'domain', 'domains':'domains', 'conditions':'conditions'}
    
    def __init__(self, operator, instanceVarOrVars, instanceExpr, domain=None, domains=None, conditions=tuple(), nestMultiIvars=False, styles=None):
        '''
        Create an Operation for the given operator that is applied over instances of the 
        given instance Variable(s), instanceVarOrVars, for the given instance Expression, 
        instanceExpr under the given conditions.  
        That is, the operation operates over all possibilities of given Variable(s) wherever
        the condition(s) is/are satisfied.  Examples include forall, exists, summation, etc.
        instanceVars may be singular or plural (iterable).  An OperationOverInstances is
        effected as an Operation over a conditional Lambda map.
        
        If nestMultiIvars is True do the following:
        When there are multiple instanceVars, this will generate a nested structure in 
        actuality and simply set the style to display these instance variables together.
        In other words, whether instance variables are joined together, like
        "forall_{x, y} P(x, y)" or split in a nested structure like
        "forall_{x} [forall_y P(x, y)]"
        is deemed to be a matter of style, not substance.  Internally it is treated as the
        latter.
              
        If a 'domain' is supplied, additional conditions are generated that each instance 
        Variable is in the domain "set": InSet(x_i, domain), where x_i is for each instance 
        variable.  If, instead, 'domains' are supplied, then each instance variable is supplied
        with its own domain (one for each instance variable).  Whether the OperationOverInstances
        is constructed with domain/domains explicitly, or they are provided as conditions in 
        the proper order does not matter.  Essentially, the 'domain' concept is simply a 
        convenience for conditions of this form and may be formatted using a shorthand notation.
        For example, "forall_{x in S | Q(x)} P(x)" is a shorthand notation for 
        "forall_{x | x in S, Q(x)} P(x)".  
        '''
        from proveit.logic import InSet
        from proveit._core_.expression.lambda_expr.lambda_expr import getParamVar
        instanceVars = compositeExpression(instanceVarOrVars)
        
        if styles is None: styles=dict()
        
        if len(instanceVars)==0:
            raise ValueError("Expecting at least one instance variable when constructing an OperationOverInstances")
        
        if domain is not None:
            # prepend domain conditions
            if domains is not None:
                raise ValueError("Provide a single domain or multiple domains, not both")
            if not isinstance(domain, Expression):
                raise TypeError("The domain should be an 'Expression' type")
            domains = [domain]*len(instanceVars)
        
        
        if domains is not None:
            # Prepend domain conditions.  Note that although we start with all domain conditions at the beginning,
            # some may later get pushed back as "inner conditions" (see below),
            if len(domains) != len(instanceVars):
                raise ValueError("When specifying multiple domains, the number should be the same as the number of instance variables.")         
            for domain in domains:
                if domain is None:
                    raise ValueError("When specifying multiple domains, none of them can be the None value")
            conditions = [InSet(instanceVar, domain) for instanceVar, domain in zip(instanceVars, domains)] + list(conditions)
            domain = domains[0]  # domain of the outermost instance variable
        conditions = compositeExpression(conditions)        
                
        # domain(s) may be implied via the conditions.  If domain(s) were supplied, this should simply reproduce
        # them from the conditions that were prepended.
        if len(conditions)>=len(instanceVars) and all(isinstance(cond, InSet) and cond.element==ivar for ivar, cond in zip(instanceVars, conditions)):
            domains = [cond.domain for cond in conditions[:len(instanceVars)]]
            domain = domains[0] # used if we have a single instance variable or nestMultiIvars is True
            nondomain_conditions = conditions[len(instanceVars):]
        else:
            domain = domains = None
            nondomain_conditions = conditions
        
        if len(instanceVars) > 1:
            if nestMultiIvars:
                # "inner" instance variable are all but the first one.
                inner_instance_vars = instanceVars[1:]
                inner_instance_param_vars = set(getParamVar(ivar) for ivar in inner_instance_vars)

                # start with the domain conditions
                if domains is None:
                    conditions = [] # no domain conditions
                    inner_conditions = [] # inner or outer
                else:
                    inner_conditions = conditions[1:len(domains)] # everything but the outer domain condition
                    conditions = [conditions[0]] # outer domain condition
                
                # Apart from the domain conditions, the "inner" conditions start with the
                # first one that has any free variables that include any of the "inner" instance variables.
                for k, cond in enumerate(nondomain_conditions):
                    if not cond.freeVars().isdisjoint(inner_instance_param_vars):
                        inner_conditions += nondomain_conditions[k:]
                        nondomain_conditions = nondomain_conditions[:k]
                        break
                
                # Include the outer non-domain conditions.
                conditions += nondomain_conditions
                
                # the instance expression at this level should be the OperationOverInstances at the next level.
                innerOperand = self._createOperand(inner_instance_vars, instanceExpr, conditions=inner_conditions)
                instanceExpr = self.__class__._make(['Operation'], dict(styles), [operator, innerOperand])
                styles['instance_vars'] = 'join_next' # combine instance variables in the style
                instanceVarOrVars = instanceVar = instanceVars[0]
            else:
                self.instanceVars = instanceVarOrVars = instanceVars
                self.domains = domains # Domain for each instance variable
        else:
            instanceVarOrVars = instanceVar = instanceVars[0]
            styles['instance_vars'] = 'no_join' # no combining instance variables in the style

        Operation.__init__(self, operator, OperationOverInstances._createOperand(instanceVarOrVars, instanceExpr, conditions), styles=styles)

        self.instanceExpr = instanceExpr
        '''Expression corresponding to each 'instance' in the OperationOverInstances'''
        
        if not hasattr(self, 'instanceVars'):
            self.instanceVar = instanceVar
            '''Outermost instance variable (or iteration of indexed variables) of the OperationOverInstance.'''
            self.domain = domain
            '''Domain of the outermost instance variable (may be None)'''
        
        self.conditions = conditions
        '''Conditions applicable to the outermost instance variable (or iteration of indexed variables) of the OperationOverInstance.  May include an implicit 'domain' condition.'''
        
        """
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
                    self.domain_or_domains = self.domains = ExprTuple(*domains)
        """
    
    def hasDomain(self):
        if hasattr(self, 'domains'):
            return True
        return self.domain is not None
                        
    @staticmethod
    def _createOperand(instanceVars, instanceExpr, conditions):
        return Lambda(instanceVars, instanceExpr, conditions)
    
    @classmethod
    def extractInitArgValue(operationClass, argName, operator, operand):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value as determined by the
        given operator and operand for an OperationOverInstances
        Expression.
        
        Override this if the __init__ argument names are different than the
        default.
        '''
        init_argname_mapping = operationClass._init_argname_mapping_
        argName = init_argname_mapping.get(argName, argName)
        assert isinstance(operand, Lambda), "Expecting OperationOverInstances operand to be a Lambda expression"
        if argName=='operator':
            return operator
        if argName=='domain' or argName=='domains': 
            return None # specify domains implicitly through conditions
        elif argName=='instanceVarOrVars':
            return singleOrCompositeExpression(operand.parameters)
        elif argName=='instanceExpr':
            return operand.body
        elif argName=='conditions':
            return operand.conditions
    
    def extractMyInitArgValue(self, argName):
        '''
        Return the most proper initialization value for the
        initialization argument of the given name in order to
        reconstruct this Expression in its current style.
        '''
        init_argname_mapping = self.__class__._init_argname_mapping_
        argName = init_argname_mapping.get(argName, argName)
        if argName=='operator':
            return self.operator # simply the operator
        elif argName=='instanceVarOrVars':
            # return the joined instance variables according to style.
            return singleOrCompositeExpression(
                OperationOverInstances.explicitInstanceVars(self))
        elif argName=='instanceExpr':
            # return the inner instance expression after joining the
            # instance variables according to the style
            return OperationOverInstances.explicitInstanceExpr(self)
        elif argName=='domain' or argName=='domains':
            # return the proper single domain or list of domains
            if self.domain is None: return None
            domains = OperationOverInstances.explicitDomains(self)
            if domains == [self.domain]*len(domains):
                return self.domain if argName=='domain' else None
            elif not None in domains:
                return ExprTuple(*domains) if argName=='domains' else None
            return None
        elif argName=='conditions':
            # return the joined conditions excluding domain conditions
            return singleOrCompositeExpression(
                OperationOverInstances.explicitConditions(self))
        
    def _allInstanceVars(self):
        '''
        Yields the instance variable of this OperationOverInstances
        and any instance variables of nested OperationOVerInstances
        of the same type.
        Modified by wdc on 6/06/2019, modifying generator fxn name
        from allInstanceVars() to _allInstanceVars() and adding a
        separate non-generator version of the allInstanceVars() fxn
        below.
        '''
        if hasattr(self, 'instanceVars'):
            for ivar in self.instanceVars:
                yield ivar
        else:
            yield self.instanceVar
            if isinstance(self.instanceExpr, self.__class__):
                for innerIvar in self.instanceExpr.allInstanceVars():
                    yield innerIvar
    
    def allInstanceVars(self):
        '''
        Returns all instance variables of this OperationOverInstances
        and all instance variables of nested OperationOverInstances
        of the same type. Relies on the generator function
        _allInstanceVars() defined above.
        Added by wdc on 6/06/2019.
        '''
        return list(self._allInstanceVars())
    
    def _allDomains(self):
        '''
        Yields the domain of this OperationOverInstances
        and any domains of nested OperationOVerInstances
        of the same type.  Some of these may be null.
        Modified by wdc on 6/17/2019, modifying generator fxn name
        from alldomains() to _alldomains() and adding a separate
        non-generator version of the alldomains() fxn below.
        '''
        if hasattr(self, 'domains'):
            for domain in self.domains:
                yield domain
        else:
            yield self.domain
            if isinstance(self.instanceExpr, self.__class__):
                for domain in self.instanceExpr.allDomains():
                    yield domain
    
    def allDomains(self):
        '''
        Returns all domains of this OperationOverInstances
        including domains of nested OperationOverInstances
        of the same type. Relies on the generator function
        _allDomains() defined above.
        Added by wdc on 6/17/2019.
        '''
        return list(self._allDomains())
    
    def _allConditions(self):
        '''
        Yields each condition of this OperationOverInstances
        and any conditions of nested OperationOverInstances
        of the same type.
        Modified by wdc on 6/06/2019, modifying generator fxn name
        from allConditions() to _allConditions() and adding a separate
        non-generator version of the allConditions() fxn below.
        '''
        for condition in self.conditions:
            yield condition
        if isinstance(self.instanceExpr, self.__class__):
            for condition in self.instanceExpr.allConditions():
                yield condition
                
    def allConditions(self):
        '''
        Returns all conditions of this OperationOverInstances
        and all conditions of nested OperationOverInstances
        of the same type. Relies on the Python generator function
        _allConditions() defined above.
        Added by wdc on 6/06/2019.
        '''
        return list(self._allConditions())
    
    def _joinedNestings(self):
        '''
        Yield the nested levels of the OperationOverInstances that are
        joined together in the style.
        '''
        yield self
        iVarStyle = self.getStyle('instance_vars')
        if iVarStyle == 'join_next':
            assert isinstance(self.instanceExpr, self.__class__), (
                "Not expecting 'instance_vars' style to be " +
                "'join_next' unless there is nesting of the same " +
                "type of OperationOverInstances")
            for expr in self.instanceExpr.joinedNestings():
                yield expr

    def joinedNestings(self):
        '''
        Returns the nested levels of the OperationOverInstances that
        are joined together in the style. Relies on the generator
        function _joinedNestings() defined above. Added here by wdc
        on 8/25/2019.
        '''
        return list(self._joinedNestings())
    
    def explicitInstanceVars(self):
        '''
        Return the instance variables that are to be shown explicitly 
        in the formatting (as opposed to being made implicit via
        conditions) joined together at this level according to the
        style. By default, this includes all of the instance variables
        that are to be joined but this may be overridden to exclude
        implicit instance variables.
        '''
        if hasattr(self, 'instanceVars'):
            return self.instanceVars
        else:
            return [expr.instanceVar for expr in self.joinedNestings()]

    def explicitDomains(self):
        '''
        Return the domains of the instance variables that
        are joined together at this level according to the style.
        If there is no domain, return None.
        '''
        if hasattr(self, 'domains'):
            return self.domains
        else:
            domains = [expr.domain for expr in self.joinedNestings()]
            if None not in domains:
                # only show as explicit domains if none of them are None:
                return domains
        return [] # No explicitly displayed domains
    
    def explicitConditions(self):
        '''
        Return the conditions that are to be shown explicitly in the formatting
        (after the "such that" symbol "|") at this level according to the style.
        By default, this includes all of the 'joined' conditions except 
        implicit 'domain' conditions.
        '''
        from proveit.logic import InSet
        if hasattr(self, 'domains'):
            assert len(self.conditions) > len(self.domains), 'expecting a condition for each domain'
            for condition, domain in zip(self.conditions, self.domains):
                assert condition == InSet(self.instanceVar, domain)
            return self.conditions[len(self.domains):] # skip the domains
        else:
            explicit_domains = self.explicitDomains()
            conditions = []
            for expr in self.joinedNestings():
                if len(explicit_domains)==0:
                    conditions.extend(expr.conditions)
                else:
                    assert expr.conditions[0] == InSet(expr.instanceVar, expr.domain)
                    conditions.extend(expr.conditions[1:])
            return conditions

    def inclusiveConditions(self):
        '''
        Return all of the conditions at this level according to the style,
        including all of the conditions of 'joined' instance variables.
        '''
        conditions = []
        for expr in self.joinedNestings():
            conditions.extend(expr.conditions)
        return conditions
        
    def explicitInstanceExpr(self):
        '''
        Return the instance expression after joining instance variables
        according to the style.
        '''
        iVarStyle = self.getStyle('instance_vars')
        if iVarStyle == 'join_next':
            return self.instanceExpr.explicitInstanceExpr()
        return self.instanceExpr
    
    def _instanceVarLists(self):
        '''
        Yield lists of instance vars that include all of the instance
        variables (see allInstanceVars method) but grouped together
        according to the style joining instance variables together.
        '''
        iVarGroup = []
        expr = self
        while isinstance(expr, self.__class__):
            if hasattr(expr, 'instanceVars'):
                yield expr.instanceVars # grouped together intrinsically
                                        # -- no nestMultiIvars
            else:
                iVarGroup.append(expr.instanceVar)
                iVarStyle = expr.getStyle('instance_vars')
                if iVarStyle != 'join_next':
                    yield iVarGroup # this group is done
                    iVarGroup = [] # start next group
            expr = expr.instanceExpr
        assert len(iVarGroup)==0, (
            "Not expecting 'instance_vars' style to be " +
            "'join_next' unless there is nesting of the same type " +
            "of OperationOverInstances")
        
    
    def instanceVarLists(self):
        '''
        Returns lists of instance vars that include all of the instance
        variables (see allInstanceVars method) but grouped together
        according to the style joining instance variables together.
        Relies on the generator function _instanceVarLists() defined
        above. Added here by wdc on 8/25/2019.
        '''
        return list(self._instanceVarLists())

    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)

    def _formatted(self, formatType, fence=False):
        '''
        Format the OperationOverInstances according to the style
        which may join nested operations of the same type.
        '''
        # override this default as desired
        explicitIvars = list(self.explicitInstanceVars()) # the (joined) instance vars to show explicitly
        explicitConditions = ExprTuple(*self.explicitConditions()) # the (joined) conditions to show explicitly after '|'
        explicitDomains = ExprTuple(*self.explicitDomains()) # the (joined) domains
        explicitInstanceExpr = self.explicitInstanceExpr() # left over after joining instnace vars according to the style
        hasExplicitIvars = (len(explicitIvars) > 0)
        hasExplicitConditions = (len(explicitConditions) > 0)
        hasMultiDomain = (len(explicitDomains)>1 and explicitDomains != ExprTuple(*[self.domain]*len(explicitDomains)))
        outStr = ''
        formattedVars = ', '.join([var.formatted(formatType, abbrev=True) for var in explicitIvars])
        if formatType == 'string':
            if fence: outStr += '['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars: 
                if hasMultiDomain: outStr += '(' + formattedVars +')'
                else: outStr += formattedVars
            if hasMultiDomain or self.domain is not None:
                outStr += ' in '
                if hasMultiDomain:
                    outStr += explicitDomains.formatted(formatType, operatorOrOperators='*', fence=False)
                else:
                    outStr += self.domain.formatted(formatType, fence=False)                    
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += " | "
                outStr += explicitConditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '} ' + explicitInstanceExpr.formatted(formatType,fence=True)
            if fence: outStr += ']'
        if formatType == 'latex':
            if fence: outStr += r'\left['
            outStr += self.operator.formatted(formatType) + '_{'
            if hasExplicitIvars: 
                if hasMultiDomain: outStr += '(' + formattedVars +')'
                else: outStr += formattedVars
            if hasMultiDomain or self.domain is not None:
                outStr += r' \in '
                if hasMultiDomain:
                    outStr += explicitDomains.formatted(formatType, operatorOrOperators=r'\times', fence=False)
                else:
                    outStr += self.domain.formatted(formatType, fence=False)
            if hasExplicitConditions:
                if hasExplicitIvars: outStr += "~|~"
                outStr += explicitConditions.formatted(formatType, fence=False)                
                #outStr += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            outStr += '}~' + explicitInstanceExpr.formatted(formatType,fence=True)
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