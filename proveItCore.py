import re

STRING = 1
MATHML = 2

class Expression:
    def __init__(self, formatMap=None):
        # Will be the associated Statement if the Expression is
        # ever 'stated' in a particular context.
        self.statement = None
        self.formatMap = formatMap
        
    def __repr__(self):
        return ''
    def __eq__(self, other):
        return repr(self) == repr(other)
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return hash(repr(self))
    
    def __str__(self):
        return self.formatted(STRING)
    
    def formatted(self, formatType, fenced=False):
        '''
        Returns a formatted version of the expression for the given formatType
        (STRING, MATHML, ...).  If fenced is True, then parenthesis around 
        the sub-expression may be necessary to avoid ambiguity.
        '''
        if self.formatMap != None and formatType in self.formatMap:
            return self.formatMap[formatType]
        return ''
    
    def prove(self, assumptions=frozenset()):
        """
        Prove a step along the way to a theorem proof (or throw an error if the proof fails).
        Use the qed() method to proven the theorem itself.
        """
        assert self.isProven(assumptions)==True, "Proof failed: " + str(self)
        return self
    
    def qed(self):
        """
        Prove a theorem, clearing any temporary provers used to prove steps along the way.
        """
        assert len(self.freeVars()) == 0, "Only apply qed to 'theorem' statements that have no free variables."
        assert self.isProven(qedProof=True)==True, "Proof failed: " + str(self)
        return self    
    
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), qedProof=False):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.  If qedProof is True, clear any temporary provers 
        (for steps along the way) after successfully proving this statement (if not already proven).
        """
        if self.statement == None: Context.current.state(self)
        assert isinstance(self.statement, Statement)
        return self.statement.isProven(assumptions, maxDepth, qedProof)
    
    def wasProven(self, assumptions=frozenset()):
        """
        Returns True iff this statement has already be proven under the given assumptions.
        """
        if self.statement == None:
            return False
        else:
            assert isinstance(self.statement, Statement)            
            return self.statement.wasProven(assumptions)
        
    def substituted(self, subMap, relabelMap = None, restrictions = None):
        '''
        Return this expression with the variables substituted 
        according to subMap (a SubstitutionMap) and/or relabeled according to 
        relabelMap (Variable:Variable dictionary).
        If supplied, restrictions is a dictionary that maps restricted Variable's
        to relabeling exceptions.  You cannot substitute with an expression that
        uses a restricted variable and you can only relabel the exception to the
        restricted variable.  This is used to protect an instance variable's 
        "scope" within an OperationOverInstances.
        '''
        return self
    
    def relabeled(self, relabelMap, restrictions=None):
        '''
        A watered down version of substitution in which only variable labels are
        changed.
        '''
        return self.substituted(subMap=SubstitutionMap(), relabelMap=relabelMap, restrictions=restrictions)
    
    def _validateRelabelMap(self, relabelMap):
        assert len(relabelMap) == len(set(relabelMap.values())), "Cannot relabel different Variables to the same Variable."
            
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        return self
    
    def usedVars(self):
        """
        Returns any variables used in the expression.
        """
        return set()
    
    def freeVars(self):
        """
        Returns the used variables that are not bound as an instance variable.
        """
        return set()    

    def safeDummyVar(self):
        return safeDummyVar([self])
    
    def specialize(self, subMap=None):
        return Context.current.specialize(self, subMap)
        
    def generalize(self, newForallVars, newConditions=None):
        if len(newForallVars) == 0 and (newConditions == None or len(newConditions) == 0):
            return self # trivial case
        return Context.current.generalize(self, newForallVars, newConditions)        

class Literal(Expression):
    def __init__(self, name, context, formatMap = None):
        Expression.__init__(self, formatMap)
        assert re.match('[A-Za-z0-9_]*', name), 'Literals must be alphanumeric or underscore.'
        self.name = name
        self.context = context
    
    def __repr__(self):
        return '\\' + repr(self.context) + '.' + self.name
    
    def formatted(self, formatType, fenced=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING:
            return self.name
        elif formatType == MATHML:
            return '<mi>' + self.name + '</mi>'

class Variable(Expression):
    def __init__(self, name, formatMap = None):
        Expression.__init__(self, formatMap)
        assert re.match('[A-Za-z0-9_]*', name), 'Variables must be alphanumeric or underscore.'
        self.name = name
        
    def __repr__(self):
        return '\\' + self.name

    def formatted(self, formatType, fenced=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING:
            return self.name
        elif formatType == MATHML:
            return '<mi>' + self.name + '</mi>'
    
    def substituted(self, subMap, relabelMap = None, restrictions = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        if (subMap != None) and (self in subMap):
            return subMap.getSub(self, restrictions)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)
            assert isinstance(subbed, Variable), "May only relabel Variable to Variable"
            if restrictions != None and subbed in restrictions.keys():
                assert self == restrictions[subbed], "Relabeling in violation of Variable restriction."
            return subbed
        return self
                
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap != None and self in varMap:
            subbed = varMap[self]
            assert isinstance(subbed, Variable), "May only relabel Variable to Variable"
            return subbed
        return self
        
    def usedVars(self):
        return {self}
        
    def freeVars(self):
        return {self}
    
class IndexVariable(Variable):
    def __init__(self, n):
        Variable.__init__(self, '_' + str(n) + '_')

def safeDummyVar(expressions):
    usedVs = frozenset().union(*[expr.usedVars() for expr in expressions])
    i = 0
    while IndexVariable(i) in usedVs:
        i += 1
    return IndexVariable(i)


class Operation(Expression):
    def __init__(self, operator, operands):
        '''
        Create an operation with the given operator and list of operands.
        '''
        Expression.__init__(self)
        assert isinstance(operator, Literal) or isinstance(operator, Variable)
        self.operator = operator
        assert len(operands) >= 1
        for operand in operands:
            assert isinstance(operand, Expression)
        self.operands = [operand for operand in operands]

    def __repr__(self):
        return self.express(repr)
    
    def formattedOperator(self, formatType):
        # override this default as desired
        return self.operator.formatted(formatType)
    
    def formatted(self, formatType, fenced=False):
        # override this default as desired
        if formatType == STRING:
            return self.formattedOperator(formatType) +  '(' + ','.join([str(operand) for operand in self.operands]) + ')'
        elif formatType == MATHML:
            outStr = '<mrow>' + self.formattedOperator(formatType) + '<mfenced>'
            for operand in self.operands: outStr += operand.formatted(formatType)
            outStr += '</mfenced></mrow>'
            return outStr
        
    def remake(self, operator, operands):
        '''
        Remake the Operation with new operator and operands, overridden to
        keep the original type where possible.
        '''
        return Operation(operator, operands)

    def remakeAndCheck(self, operator, operands):
        remade = self.remake(operator, operands)
        assert isinstance(remade, Operation), 'remake function must make an Operation type'
        assert remade.operator == operator, 'remake function must make an Operation true to its given operator'
        assert remade.operands == operands, 'remake function must make an Operation true to its given operands'
        return remade
            
    def express(self, subExpressFn):
        return subExpressFn(self.operator) + ''.join(['{' + subExpressFn(operand) + '}' 
                                                      for operand in self.operands])
    def substituted(self, subMap, relabelMap = None, restrictions = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        if restrictions == None:
            restrictions = dict()
        operator = self.operator
        subbedOperands = [operand.substituted(subMap, relabelMap, restrictions) for operand in self.operands]
        operatorSub = subMap.getSub(self.operator, restrictions)
        if operatorSub != self.operator:
            # May substitute the operator with another Literal or Variable,
            # or may substitute the entire operation.
            if isinstance(operatorSub, Literal) or isinstance(operatorSub, Variable):
                operator = operatorSub
            else:
                # Substitute the entire operation.
                # For example \f{\x}{\y} -> \INTEGERS.ADD{\x}{\y} has \f{\x}{\y}
                # as the instanceOperator and \INTEGERS.ADD{\x}{\y} as the newExpr
                # and will return the newExpr with x, y replaced with the
                # substituted respective operands of the original operator.
                newExpr, arguments = operatorSub.expression, operatorSub.arguments
                operandSubMap = SubstitutionMap()
                assert isinstance(newExpr, Expression), 'Improper operation substitution'
                assert len(subbedOperands) == len(arguments), 'Cannot substitute an operation with the wrong number of arguments'
                for i in xrange(len(subbedOperands)):
                    assert isinstance(arguments[i], Variable), 'Improper operation substitution'
                    operandSubMap.substitute(arguments[i], subbedOperands[i])
                return newExpr.substituted(operandSubMap)
        else:
            # The operator may be relabeled
            operator = self.operator.relabeled(relabelMap, restrictions)
        return self.remakeAndCheck(operator, subbedOperands)
            
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap == None:
            varMap = dict()
        genericOperator = self.operator.makeGeneric(varAssignments, varMap)
        genericOperands = [operand.makeGeneric(varAssignments, varMap) for operand in self.operands]
        return self.remakeAndCheck(genericOperator, genericOperands)
        
    def usedVars(self):
        return self.operator.usedVars().union(*[operand.usedVars() for operand in self.operands])
        
    def freeVars(self):
        return self.operator.freeVars().union(*[operand.freeVars() for operand in self.operands])

class OperationOverInstances(Operation):
    def __init__(self, operator, instanceVar, instanceExpression, condition=None):
        Operation.__init__(self, operator, [instanceExpression])
        assert isinstance(instanceVar, Variable)
        self.instanceVar = instanceVar
        assert isinstance(instanceExpression, Expression)
        self.instanceExpression = instanceExpression
        assert condition == None or isinstance(condition, Expression)
        self.condition = condition
        
    def formatted(self, formatType, fenced=False):
        # override this default as desired
        implicitIvar = self.implicitInstanceVar()
        outStr = ''
        if formatType == STRING:
            if fenced: outStr += '['
            outStr += self.formattedOperator(formatType) + '_{'
            if not implicitIvar:
                outStr += str(self.instanceVar) 
            if self.condition != None:
                if not implicitIvar: outStr += " | "
                outStr += str(self.condition)
            outStr += '} ' + str(self.instanceExpression)
            if fenced: outStr += ']'
        elif formatType == MATHML:
            if fenced: outStr += '<mfenced>'
            outStr += '<mrow><msub>' + self.formattedOperator(formatType)
            if self.condition != None: outStr += '<mrow>'
            if not implicitIvar:
                outStr += self.instanceVar.formatted(formatType)
            if self.condition != None: 
                if not implicitIvar:
                    outStr += '<mo>|</mo>'
                outStr += self.condition.formatted(formatType) + '</mrow>'
            outStr += '</msub>' + self.instanceExpression.formatted(formatType) + '</mrow>'
            if fenced: outStr += '</mfenced>'
        return outStr
    
    def implicitInstanceVar(self):
        '''
        Overloading and returning True means that the instance variable is implicit in the condition
        and doesn't need to be explicitly shown when formatted.
        '''
        return False
    
    def remake(self, operator, instanceVar, instanceExpression, condition):
        '''
        Remake the OperationOverInstances with new operator, instanceVar, instanceExpression, and condition
        overridden to keep the original type where possible.
        '''
        return OperationOverInstances(operator, instanceVar, instanceExpression, condition)

    def remakeAndCheck(self, operator, instanceVar, instanceExpr, condition):
        remade = self.remake(operator, instanceVar, instanceExpr, condition)
        assert isinstance(remade, OperationOverInstances), 'remake function must make an OperationOverInstance type'
        assert remade.operator == operator, 'remake function must make an OperationOverInstance true to its given operator'
        assert remade.instanceVar == instanceVar, 'remake function must make an OperationOverInstance true to its given instanceVar'
        assert remade.instanceExpression == instanceExpr, 'remake function must make an OperationOverInstance true to its given instanceExpression'
        assert remade.condition == condition, 'remake function must make an OperationOverInstance true to its given condition'
        return remade
        
    def express(self, subExpressFn):
        if self.condition == None:
            instanceVarsStr = '[' + subExpressFn(self.instanceVar) + ']' 
        else:
            instanceVarsStr = '[' + subExpressFn(self.instanceVar) + '|' + subExpressFn(self.condition) + ']' 
        operandsStr = '{' + subExpressFn(self.instanceExpression) + '}' 
        return subExpressFn(self.operator) + instanceVarsStr + operandsStr
    
    def substituted(self, subMap, relabelMap = None, restrictions = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        An instance variable has its own scope within the 
        OperationOverInstance and does not get substituted.
        It may be relabeled, however.
        '''
        if restrictions == None:
            restrictions = dict()
        operator = self.operator
        operatorSub = subMap.getSub(self.operator, restrictions)
        if operatorSub != operator:
            # May only substitute the operator with another Literal or Variable.
            assert isinstance(operatorSub, Literal) or isinstance(operatorSub, Variable)
            operator = operatorSub
        else:
            # Or we may relabel it
            operator = operator.relabeled(relabelMap, restrictions)
        innerSubMap = subMap
        if self.instanceVar in subMap.getSubstitutingVars():
            # can't substitute the instanceVar; it's in a new scope.
            innerSubMap = subMap.copy()
            innerSubMap.pop(self.instanceVar)
        # we can relabel the instanceVar, however
        origInstanceVar = self.instanceVar
        instanceVar = self.instanceVar.relabeled(relabelMap, restrictions)
        # the instance variable is restricted in the scope of the condition and instance expression
        innerRestrictions = dict(restrictions)
        innerRestrictions[instanceVar] = origInstanceVar
        # the condition with the substitution
        subbedCondition = None
        if self.condition != None:
            subbedCondition = self.condition.substituted(innerSubMap, relabelMap, innerRestrictions)
        # the instanceExpression with the substitution:
        subbedInstanceExpr = self.instanceExpression.substituted(innerSubMap, relabelMap, innerRestrictions)
        return self.remakeAndCheck(operator, instanceVar, subbedInstanceExpr, subbedCondition)
    
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap == None:
            varMap = dict()
        genericOperator = self.operator.makeGeneric(varAssignments, varMap)
        varAssignments.append(self.instanceVar)
        genericInstanceVar = IndexVariable(len(varAssignments))
        varMap[self.instanceVar] = genericInstanceVar
        genericCondition = None
        if self.condition != None:
            genericCondition = self.condition.makeGeneric(varAssignments, varMap)
        genericInstanceExpr = self.instanceExpression.makeGeneric(varAssignments, varMap)
        return self.remakeAndCheck(genericOperator, genericInstanceVar, genericInstanceExpr, genericCondition)

    def freeVars(self):
        fvars = Operation.freeVars(self)
        # the instance variable is not free
        fvars.discard(self.instanceVar)
        return fvars

class Function:
    '''
    A function is defined by an expression and zero or more argument variables
    that are in the expression.  For example, f(x, y) = sin(x^2 + y), would be defined
    by the expression sin(x^2 + y) and [x, y] as the argument variables. 
    '''
    def __init__(self, expression, arguments):
        assert isinstance(expression, Expression)
        for arg in arguments:
            assert isinstance(arg, Variable)
        self.expression = expression
        self.arguments = tuple(arguments)
        
    def __str__(self):
        return "{" + ", ".join([str(argument) for argument in self.arguments]) + "} -> " + str(self.expression)

    def __repr__(self):
        return "{" + ", ".join([repr(argument) for argument in self.arguments]) + "} -> " + repr(self.expression)
    def __eq__(self, other):
        return repr(self) == repr(other)
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return hash(repr(self))
        
    def usedVars(self):
        return self.expression.usedVars() | set(self.arguments)

class SubstitutionMap(dict):
    def __init__(self, subMap = None):
        if subMap != None:
            dict.__init__(self, subMap)
        
    def substitute(self, variable, value):
        '''
        Indicate that the given variable should be replaced by the
        given value for the substitution. 
        '''
        assert isinstance(variable, Variable)
        assert isinstance(value, Expression)
        self[variable] = value
        
    def substituteOp(self, operator, function):
        '''
        Indicate that any operation using the given operator variable
        should be replaced by the given function, taking the operation's
        operands as the arguments passed in to the function.
        '''
        assert isinstance(operator, Variable)
        assert isinstance(function, Function)
        self[operator] = function
        
    def getSubstitutingVars(self):
        return self.keys()
    
    def getSub(self, var, restrictions = None):
        if var in self.keys():
            subbed = self[var]
            if isinstance(subbed, Function):
                # this is an operation substitution
                introducedVars = subbed.expression.freeVars()
                introducedVars.difference_update(subbed.arguments)
                assert restrictions == None or introducedVars.isdisjoint(restrictions.keys()), 'Must not make substitution with reserved variables (i.e. an instance variable)'
            else:
                assert restrictions == None or subbed.freeVars().isdisjoint(restrictions.keys()), 'Must not make substitution with reserved variables (i.e. an instance variable)'
            return subbed
        return var
    
    def makeImmutableForm(self):
        return tuple(self.items())
    
    def copy(self):
        return SubstitutionMap(self)
            
def asStatement(statementOrExpression):
    '''
    Given an expression, returns the corresponding statement (made in the current context).
    Given a statement, returns what was given.
    '''
    if isinstance(statementOrExpression, Statement):
        return statementOrExpression
    return Context.current.state(statementOrExpression).statement

class PythonVar:
    def __init__(self, methodName, varName):
        self.methodName = methodName
        self.varName = varName
    def __str__(self):
        return self.varName + " from " + self.methodName
    
class Statement:
    ProofCount = 0 # counter to number each proof
    utilizedProofNumbers = set() #  don't remove from _assumptionSetsForWhichProven of a ProofStepInfo unless it's proofnumber is not utilized
    
    def __init__(self, genericExpression):
        # this is the generic expression, with instance variables replaced by indices
        self._genericExpression = genericExpression
        genericExpression.statement = self
        # contexts in which the statement appears with named instance variables
        self._contexts = set()
        self._hypothesisOfImplication = None
        self._conclusionOfImplication = None
        self._implicationsOfHypothesis = set()
        self._implicators = set()
        self._specializers = set()
        self._generalizers = set()
        self._specializations = set()
        self._generalizations = set()
        self._isAxiom = False
        # sets of assumptions for which we'll use reasoning by hypothesis to prove the statement
        self._reasonByHypothesisAssumptions = list()
#        self._proofStepInfo = Statement.ProofStepInfo(self) # information regarding proofs for various assumption sets
        self._registeredVar = None # (module_name, variable_name) tuple that refers to this statement and is registered
        self.proofNumber = float("inf") # number each proof for statements proven with no assumptions necessary
        self._prover = None # a Prover that proves this statement if it has no free variables and has been proven (theorem)
        
    '''
    class ProofAssumptions:
        def __init__(self, assumptionSet):
            self.assumptionSet = frozenset(assumptionSet)
            Statement.ProofCount += 1
            self.proofNumber = Statement.ProofCount
            
    class ProofStepInfo:
        def __init__(self, stmtToProve):
            # for each set of proving statements, store the assumptions for which the statement has been proven
            self._stmtToProve = stmtToProve
            self._assumptionSetsForWhichProven = {tuple():[{stmtToProve}]} # any statement is proven by self assumption
        
        def markAsProven(self, provingStatements, assumptions):
            if not provingStatements in self._assumptionSetsForWhichProven.keys():
                self._assumptionSetsForWhichProven[provingStatements] = []
            pAssumptionSets = self._assumptionSetsForWhichProven[provingStatements]
            if any([pAssumptions.issubset(assumptions) for pAssumptions in pAssumptionSets]):
                return # already covered by a subset of the assumptions
            # remove any in _assumptionSetsForWhichProven that the current set of assumptions already covers
            pAssumptionSets = [pAssumptions for pAssumptions in pAssumptionSets if not assumptions.issubset(pAssumptions)]
            pAssumptionSets.append(assumptions)
            self._assumptionSetsForWhichProven[provingStatements] = pAssumptionSets
            if len(assumptions) == 0:
                # proof without assumptions -- possibly a theorem proof
                Statement.ProofCount += 1
                self._stmtToProve.proofNumber = Statement.ProofCount

        def provenAssumptions(self, provingStatements, assumptions):
            """
            Returns the smallest subset of the assumptions for which this statement was proven
            by the given provingStatements or None if it isn't proven for these assumptions.
            """
            setOfProvenAssumptions = [provenAssumptions for provenAssumptions in self._assumptionSetsForWhichProven[provingStatements] if provenAssumptions.issubset(assumptions)]
            if len(setOfProvenAssumptions) == 0:
                return None
            return min(setOfProvenAssumptions, key = lambda assumptions : len(assumptions))
        
        def provingStatements(self, assumptions):
            """
            Returns the set of statements that prove this statement under the given assumptions
            or None if it hasn't been proven for these assumptions.  Any unnecessary assumptions
            will be removed from the set of assumptions that was provided.
            """
            # Get set of proven assumptions for each set of proving statements
            setOfProvenAssumptions = {pStatements:self.provenAssumptions(pStatements, assumptions) for pStatements in self._assumptionSetsForWhichProven.keys()}
            # remove those providing no proof
            setOfProvenAssumptions = {pStatements:pAssumptions for (pStatements, pAssumptions) in setOfProvenAssumptions.iteritems() if pAssumptions != None}
            if len(setOfProvenAssumptions) == 0:
                return None # no such proof
            # get the provingStatements and provenAssumptions with the fewest proven assumptions
            (pStatements, pAssumptions) = min(setOfProvenAssumptions.iteritems(), key = lambda stmtsAndAssumptions : len(stmtsAndAssumptions[1]))
            assert assumptions.issuperset(pAssumptions)
            # update assumptions -- should then be the same as provenAssumptions
            assumptions.intersection_update(pAssumptions)
            return pStatements

    def provingStatements(self, assumptions):
        """
        Returns the set of statements that prove this statement under the given assumptions
        or None if it hasn't been proven for these assumptions.  Any unnecessary assumptions
        will be removed from the set of assumptions that was provided.
        """
        return self._proofStepInfo.provingStatements(assumptions)

    def provenAssumptions(self, assumptions):
        """
        Returns the subset of assumptions for which this statement is proven
        or None if it hasn't been proven for these assumptions.
        """
        pAssumptions = set(assumptions)
        pStatements = self.provingStatements(pAssumptions)
        return pAssumptions if pStatements != None else None
    '''
             
    def __str__(self):
        return str(self.getExpression())
    
    def registerPythonVar(self, pyVar):
        """
        Register the statement to a given variable identified by a PythonVar.
        """
        assert isinstance(pyVar, PythonVar)
        assert len(self.freeVars()) == 0, 'May only register statements with no free variables (a potential theorem)'
        if not self.wasProven():
            print 'Warning: registering an unproven theorem,', str(pyVar)
        if self._registeredVar != None and self._registeredVar != pyVar:
            print 'Warning: overwriting theorem registration,', str(self._registeredVar), 'now', str(pyVar)
        self._registeredVar = pyVar
        
    def getRegisteredPythonVar(self):
        """
        Returns the PythonVar identifying the variable for which this 
        Statement has been registered, or None if no variable has been registered to it.
        """
        return self._registeredVar
        
    def getContexts(self):
        return list(self._contexts)
    
    def getExpressions(self, context):
        return [self.getExpression(varAssignments) for varAssignments in context.statementVarAssignments[self]]
        
    def getExpression(self, varAssignments=None):
        if varAssignments == None:
            # use any assignments in any context
            context = list(self._contexts)[0]
            varAssignments = context.statementVarAssignments[self][0]
        varMap = {IndexVariable(n+1) : varAssignments[n] for n in xrange(len(varAssignments))}
        return self._genericExpression.relabeled(varMap)
    
    def freeVars(self):
        return self.getExpression().freeVars()
    
    def addContext(self, context):
        self._contexts.add(context)
    
    def reasonByHypothesis(self, assumptions=frozenset()):
        '''
        Indicate that we should use hypothetical reasoning to prove this statement
        when the specified assumptions (or more) are made.
        '''
        assumptions = {asStatement(assumption) for assumption in assumptions}
        for assumption in assumptions:
            assert isinstance(assumption, Statement)
        for prevAssumptions in self._reasonByHypothesisAssumptions:
            if prevAssumptions.issubset(assumptions):
                return # redundant, already covered by previous assumptions
        self._reasonByHypothesisAssumptions.append(assumptions)
        
    def _useHypotheticalReasoning(self, assumptions):
        return True
        #for qualifyingAssumptions in self._reasonByHypothesisAssumptions:
        #    if qualifyingAssumptions.issubset(assumptions):
        #        return True
        #return False
        
    def makeAxiom(self):
        self._isAxiom = True
        self._markAsProven(Statement.Prover(self, []))
#        self._proofStepInfo.markAsProven(tuple(), set()) # trivially "proven"
    
    def isAxiom(self):
        return self._isAxiom
    
    def isTheorem(self):
        '''
        Our definition of a theorem is a statement known to be true that has no free variables.
        '''
        return self.wasProven() and len(self._genericExpression.freeVars()) == 0
        
    def addSpecializer(self, original, subMap, conditions):
        self._specializers.add((original, subMap.makeImmutableForm(), tuple([asStatement(condition) for condition in conditions])))
        original._specializations.add(self)

    def addGeneralizer(self, original, forallVars, conditions):
        conditions = tuple() if conditions == None else conditions
        self._generalizers.add((original, tuple(forallVars), tuple([asStatement(condition) for condition in conditions])))
        original._generalizations.add(self)
        
    def addImplicator(self, hypothesis, implication):
        if (hypothesis, implication) in self._implicators:
            return # already in implicators list
        self._implicators.add((hypothesis, implication))
        implication._hypothesisOfImplication = hypothesis
        implication._conclusionOfImplication = self
        hypothesis._implicationsOfHypothesis.add(implication)
            
    class Prover:
        # Temporary provers: mapping a statement to a list of provers (for various assumption sets).
        # After proving a theorem via the qed method, the temporary provers will be cleared.
        _tmpProvers = dict()
        
        def __init__(self, stmtToProve, assumptions, impliedParent=None, proverType="root", newAssumptionsInOrder=None):
            # if this is proven, along with any corequisites, the impliedParent is also proven
            assert impliedParent != self
            self.impliedParent = impliedParent 
            self.stmtToProve = stmtToProve
            self.assumptions = frozenset(assumptions)
            self.proverType = proverType
            if impliedParent == None:
                self.depth = 0
            else:
                self.depth = impliedParent.depth+1
            self.corequisites = [self]
            self.provers = None # when proven, what Prover's prover the proof for this one
            # subset of the assumptions which proves self.stmtToProve
            self.provingAssumptions = None
            if self.stmtToProve.isAxiom():
                self.provingAssumptions = frozenset()
            elif self.stmtToProve.wasProven(assumptions):
                self.provingAssumptions = self.stmtToProve.provingAssumptions(assumptions)
                self.provers = self.stmtToProve.getProver(assumptions).provers
            elif stmtToProve in assumptions:
                self.provingAssumptions = frozenset([stmtToProve])
#            # see whether or not it was already proven for a subset of the assumptions
#            if self.stmtToProve.provingStatements(self.provingAssumptions) == None:
#                self.provingAssumptions = None
            # For keeping the order of the new assumptions
            if newAssumptionsInOrder == None:
                self.newAssumptionsInOrder = tuple()
            else:
                self.newAssumptionsInOrder = tuple(newAssumptionsInOrder) 
        
        def isCircular(self, assumptions=None):
            '''
            Make sure we aren't stuck in circular logic.  Returns True if this derivation
            step is trying to prove itself up the chain under the given assumptions
            (default uses the assumptions of this Prover).
            '''
            if assumptions == None:
                assumptions = self.assumptions
            prover = self.impliedParent
            while prover != None:
                if prover.stmtToProve == self.stmtToProve and assumptions.issubset(prover.assumptions):
                    return True # can't prove a statement via itself and no additional assumptions
                prover = prover.impliedParent
            return False
        
        def requirementsSatisfied(self):
            '''
            Is stmtToProve and any corequisite satisfied such that impliedParent is implied?
            '''
            return all([corequisite.wasProven() for corequisite in self.corequisites])
        
        def satisfyingAssumptions(self):
            provingAssumptionSets = [corequisite.provingAssumptions for corequisite in self.corequisites]
            return frozenset().union(*provingAssumptionSets)
        
        def completesProof(self):
            '''
            Go up the tree of impliedParents as long as requirements are satisfied, returning True
            if we get to the root.  While going up, records the first Provers to prove a Prover.
            '''
            prover = self
            while prover.requirementsSatisfied():
                #print prover, prover.depth
                satAssumptions = prover.satisfyingAssumptions()
#                provingStatements = frozenset({pvr.stmtToProve for pvr in prover.corequisites})
                provers = prover.corequisites
                prover = prover.impliedParent
                if prover == None:
                    return True # main statement is proven
                prover.provers = provers
                # note that hypothetical reasoning and generalization condition 
                # assumptions get eliminated as we move up
                satAssumptions &= prover.assumptions
                prover.provingAssumptions = satAssumptions # proven by child(ren)
#                prover.stmtToProve._markAsProven(satAssumptions, prover)
                # remember that it is proven for this set of assumptions
#                #prover.stmtToProve.proofStepInfo.markAsProven(provingStatements, satAssumptions)
            return False
        
        def redundant(self):
            '''
            If any ancestor was already proven, this is redundant.
            '''
            prover = self
            if prover.wasProven(): return True
            while prover.impliedParent != None:
                prover = prover.impliedParent
                if prover.wasProven(): return True
            return False

        def wasProven(self):
            return self.provingAssumptions != None 
            
        def appendProvers(self, breadth1stQueue):
            '''
            Append any provers that can implicate that self is proven.
            '''
            stmt = self.stmtToProve
            # Prove by specialization?  Put this at front to connect with a theorem first if possible,
            for original, subMap, conditions in stmt._specializers:
                subMap = SubstitutionMap(subMap)
                mappedConditions = {asStatement(condition.getExpression().substituted(subMap)) for condition in conditions}
                generalityProver = Statement.Prover(original, self.assumptions - mappedConditions, self, "specialization")
                corequisites = [generalityProver] + [Statement.Prover(condition, self.assumptions, self, "specialization condition") for condition in mappedConditions]
                for prover in corequisites:
                    prover.corequisites = corequisites
                #print [corequisite.stmtToProve.getExpression() for corequisite in corequisites]
                breadth1stQueue += corequisites
            # Prove by generalization?
            for original, forallVars, conditions in stmt._generalizers:
                # we cannot allow assumptions that have any of the forallVars as free variables
                subAssumptions = {assumption for assumption in self.assumptions if len(assumption.freeVars() & set(forallVars)) == 0}            
                # add assumptions for any of the conditions of the generalizer
                subAssumptions |= set(conditions)
                breadth1stQueue.append(Statement.Prover(original, subAssumptions, self, "generalization", newAssumptionsInOrder=conditions))
            # Truth by implication?
            for (hypothesis, implication) in stmt._implicators:
                # both hypothesis and implication must be proven for this to be sufficient, so they are cross requirements
                implicationProver = Statement.Prover(implication, self.assumptions, self, "implication")
                hypothesisProver = Statement.Prover(hypothesis, self.assumptions, self, "hypothesis")
                implicationProver.corequisites = hypothesisProver.corequisites = [implicationProver, hypothesisProver]
                breadth1stQueue += (implicationProver, hypothesisProver)
            # Prove by hypothetical reasoning?
            if stmt._useHypotheticalReasoning(self.assumptions) and stmt._hypothesisOfImplication != None:
                hypothesis = stmt._hypothesisOfImplication
                breadth1stQueue.append(Statement.Prover(stmt._conclusionOfImplication, self.assumptions | {hypothesis}, self, "hypothetical reasoning"))

    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), qedProof=False):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.  If qedProof is True, clear the temporary provers after
        successfully proving this statement (if not already proven).
        """
        assumptions = {asStatement(assumption) for assumption in assumptions}
        if self.wasProven(assumptions):
            return True
        rootProver = Statement.Prover(self, assumptions) 
        breadth1stQueue = [rootProver]
        while len(breadth1stQueue) > 0:
            prover = breadth1stQueue.pop(0)
            #print prover.stmtToProve, prover.depth, [assumption.getExpression() for assumption in prover.assumptions]
            if prover.isCircular(): continue
            if prover.completesProof():
                print "proven at depth", prover.depth
                self._markAsProven(rootProver)
                if qedProof:
                    Statement.Prover._tmpProvers.clear() # clear temporary provers after QED
                return True
            if prover.depth < maxDepth and not prover.redundant():
                prover.appendProvers(breadth1stQueue)
        return False
    
    def _markAsProven(self, prover):
        assumptions = prover.assumptions
        if len(assumptions) == 0 and len(self.freeVars()) == 0:
            # theorem-level proof
            self._prover = prover 
            Statement.ProofCount += 1
            self.proofNumber = Statement.ProofCount
            # any other provers are obsolete
            Statement.Prover._tmpProvers.pop(self, None)
        if not self in Statement.Prover._tmpProvers:
            Statement.Prover._tmpProvers[self] = []
        provers = Statement.Prover._tmpProvers[self] 
        # remove any that are made obsolete
        provers = [prover for prover in provers if assumptions.issubset(prover.assumptions)]
        if not any([prover.assumptions.issubset(assumptions) for prover in provers]):
            # only add the prover if it isn't redundant
            provers.append(prover)
        Statement.Prover._tmpProvers[self] = provers
    
    def getOrMakeProver(self, assumptions=frozenset()):
        '''
        If this statement was proven, returns the Prover that proves this statement;
        otherwise, returns a new Prover to be used to find the proof or explore the possibilities.
        '''
        prover = self.getProver(assumptions)
        if prover != None:
            return prover
        return Statement.Prover(self, assumptions)
    
    def getProver(self, assumptions=frozenset()):
        '''
        If this statement was proven under the given assumptions and this proof is to be
        remembered (i.e., not a clear temporary proof), returns the Prover that proves 
        this statement; otherwise, returns None.
        '''
        if self._prover != None:
            return self._prover # proof requiring no assumptions
        assumptions = frozenset(assumptions)
        if not self in Statement.Prover._tmpProvers: 
            return None # no temporary provers that may prove this
        for prover in Statement.Prover._tmpProvers[self]:
            provenAssumptions = prover.assumptions
            if assumptions.issuperset(provenAssumptions):
                return prover
        return None
    
    def wasProven(self, assumptions=frozenset()):
        """
        Returns True iff this statement has been proven under the given assumptions
        and it is a proof that is remembered (i.e., not a clear temporary proof).
        """
        return self.getProver(assumptions) != None

    def provingAssumptions(self, assumptions=frozenset()):
        """
        Returns the subset of the assumptions that proves the statement,
        or None if no such proof was made or remembered.
        """
        prover = self.getProver(assumptions)
        if prover == None: return None
        return prover.assumptions
    
class Context:
    # All statements for any context.  
    contexts = dict()
    statements = dict()
    current = None

    def __init__(self, name, setAsCurrentContext=False):
        # map "unique" internal expression representations to corresponding statements
        # which can map to one or more equivalent expressions (that may have different
        # external representations)
        self.literals = dict()
        assert re.match('[A-Z][A-Z0-9_]*', name), 'Context names must be alphanumeric or underscore, starting with a alphabet character, and with only capitalized alphabet characters.'
        self.name = name
        Context.contexts[name] = self
        # For each statement, we have a list of lists of Variables that
        # are used to build expressions from the generic expression (indexed variables)
        # of the statement.
        self.statementVarAssignments = dict()
        if setAsCurrentContext:
            Context.current = self
        else:
            Context.current = None # to play it safe,=

    def __repr__(self):
        return self.name

    def addLiteral(self, name, formatMap=None):
        if not name in self.literals:
            self.literals[name] = Literal(name, self, formatMap)
        return self.literals[name]
    
    def getLiteral(self, name):
        return self.literals[name]
    
    def state(self, expression):
        '''
        Make a Statement from the given Expression.  All of its instance variables 
        will be replaced with generic indices for storage in the statements database, 
        equating statements that differ only by instance variable labels.  The original 
        expression will be returned, but will be linked with its corresponding statement.
        '''
        from basicLogic import IMPLIES
        if isinstance(expression, Operation) and expression.operator == IMPLIES and len(expression.operands) == 2:
            # When stating an Implication, link the consequence to the
            # condition as an implicating Statement.
            implication = self._makeStatement(expression)
            hypothesis = self.state(expression.operands[0]).statement
            conclusion = self.state(expression.operands[1]).statement
            conclusion.addImplicator(hypothesis, implication)
        else:
            self._makeStatement(expression)
        return expression

    def stateAxiom(self, expression):
        '''
        Make a Statement in the same way as the state(..) function, but also set its
        axiom flag.  An axiom may not have any free variables.
        '''
        freeVars = expression.freeVars()
        assert len(freeVars) == 0, 'Expressions with free variable may not be converted to a statement (bind with an OperationOverInstances): ' + str(freeVars)
        statement = self.state(expression).statement
        statement.makeAxiom()
        return expression

    def _makeStatement(self, expression):
        # find/add the statement and return it.
        varAssignments = []
        genericExpression = expression.makeGeneric(varAssignments)
        rep = repr(genericExpression)
        statement = Context.statements.setdefault(rep, Statement(genericExpression))
        statement.addContext(self)
        self.statementVarAssignments.setdefault(statement, []).append(varAssignments)
        expression.statement = statement
        return statement
    
    def specialize(self, original, subMap):
        '''
        State and return a specialization of a given original statement
        which derives from the original statement via a specialization inference
        rule.  That is, return the specialized form of the 'original' expression 
        by substituting one or more instance variables of outer Forall operations 
        according to the given substitution map.  It may have free variables which can be 
        considered to be "arbitrary" variables used in logical reasoning.  Eventually
        they should be bound again via generalization (the counterpart to specialization).
        '''
        from basicLogic import FORALL, Implies
        subMap = SubstitutionMap(subMap)
        substitutingVars = set(subMap.getSubstitutingVars())
        instanceVars = set()
        conditions = set()
        expr = original
        while isinstance(expr, OperationOverInstances) and expr.operator == FORALL:
            instanceVars.add(expr.instanceVar)
            if expr.condition != None: conditions.add(expr.condition)
            expr = expr.instanceExpression
        # any remaining variables may be used only for relabeling
        relabelVars = substitutingVars.difference(instanceVars)
        for relabelVar in relabelVars:
            assert isinstance(subMap.getSub(relabelVar), Variable), 'May only specialize by substituting instance variables of nested forall operations or otherwise simply relabeling variables with variables.'
        relabMap = {k:v for k,v in subMap.items() if k in relabelVars}
        nonRelabSubMap = SubstitutionMap({k:v for k,v in subMap.items() if k not in relabelVars})
        specializedExpr = self.state(expr.substituted(nonRelabSubMap, relabelMap = relabMap))
        if original.statement == None: self.state(original)
        specializedExpr.statement.addSpecializer(original.statement, subMap, conditions)
        return specializedExpr        
                       
    def generalize(self, original, newForallVars, newConditions=None):
        '''
        State and return a generalization of a given original statement
        which derives from the original statement via a generalization inference
        rule.  This is the counterpart of specialization.  Where the original 
        has free variables taken to represent any particular 'arbitrary' values, 
        the  generalized form is a forall statement over some or all of these once
        free variables.  That is, it is statement applied to all values of any 
        of the once free variables under the given conditions.  Any condition 
        restriction is allowed because it only weakens the statement relative 
        to no condition.
        '''
        from basicLogic import Forall, Implies
        generalizedExpr = self.state(Forall(newForallVars, original, newConditions))
        # In order to be a valid tautology, we simply have to make sure that the expression is zero or more
        # nested Forall operations with the original as the inner instanceExpression.
        if original.statement == None: self.state(original)
        if newConditions != None:
            print str(generalizedExpr)
            print "conditions", [str(condition) for condition in newConditions]
        generalizedExpr.statement.addGeneralizer(original.statement, newForallVars, newConditions)
        self._checkForallInstanceExpr(generalizedExpr, original)
        return generalizedExpr
    
    def _checkImplication(self, expr, hypothesis, conclusion):
        '''
        Make sure the created implies statement is what it is supposed to be.
        '''
        from basicLogic import IMPLIES
        assert isinstance(expr, Operation)
        assert expr.operator == IMPLIES
        assert len(expr.operands) == 2 and expr.operands[0] == hypothesis and expr.operands[1] == conclusion

    def _checkForallInstanceExpr(self, expr, instanceExpr):
        '''
        Make sure the expr contains the instanceExpr in zero or more nested Forall operations.
        '''
        from basicLogic import FORALL
        while expr != instanceExpr:
            assert isinstance(expr, OperationOverInstances) and expr.operator == FORALL
            expr = expr.instanceExpression
    
defaultContext = Context('DEFAULT')
    
def statement(expr):
    if isinstance(expr, Statement):
        return expr
    if expr.statement == None:
        Context.current.state(expr)
    return expr.statement

def registerTheorems(moduleName, variables):
    for vName, v in variables.iteritems():
        if isinstance(v, Expression) and v.statement != None and len(v.freeVars()) == 0:
            v.statement.registerPythonVar(PythonVar(moduleName, vName))
