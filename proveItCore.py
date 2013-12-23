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
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        assert self.isProven(assumptions)==True, "Proof failed: " + str(self) + " given " + makeAssumptionsStr(assumptions)
        return self
    
    def check(self, assumptions=frozenset()):
        """
        Check that this statement is true under the given assumptions but not for a step
        of a theorem proof (that is, temporary provers aren't stored).
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        assert self.isProven(assumptions, markProof=False)==True, "Proof failed: " + str(self) + " given " + makeAssumptionsStr(assumptions)
        return self
    
    def qed(self):
        """
        Prove a theorem, clearing any temporary provers used to prove steps along the way.
        """
        assert len(self.freeVars()) == 0, "Only apply qed to 'theorem' statements that have no free variables."
        assert self.isProven(qedProof=True)==True, "Proof failed: " + str(self)
        return self    
    
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True, qedProof=False):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.  If qedProof is True, clear any temporary provers 
        (for steps along the way) after successfully proving this statement (if not already proven).
        """
        if self.statement == None: Statement.state(self)
        assert isinstance(self.statement, Statement)
        return self.statement.isProven(assumptions, maxDepth, markProof, qedProof)
    
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
    
    def state(self):
        return Statement.state(self)
    
    def specialize(self, subMap=None):
        (specialization, conditions) = Statement.specialize(self, subMap)
        return specialization.check({self} | conditions)
        
    def generalize(self, newForallVars, newConditions=None):
        if len(newForallVars) == 0 and (newConditions == None or len(newConditions) == 0):
            return self # trivial case
        return Statement.generalize(self, newForallVars, newConditions) #.check({self})
    
    def show(self, assumptions=frozenset()):
        '''
        Show the derivation tree of the proof or partial proof for
        proving the Statement of this Expression under the given
        assumptions.
        '''
        from derivationTreeView import showTreeView
        showTreeView([self.state().statement.getOrMakeProver(assumptions)])
    
    def proveThenShow(self, assumptions=frozenset()):
        '''
        First attempt to prove the Statement of this Expression, then
        show the derivation tree of the proof.
        '''
        self.prove(assumptions).show(assumptions)
    
    def evaluate(self):
        assert False, "evaluate() not implemented for this type"
    
    def proveByEval(self):
        return self.evaluate().deriveFromBooleanEquality().prove()

class Literal(Expression):
    def __init__(self, name, context, formatMap = None):
        Expression.__init__(self, formatMap)
        assert re.match('[A-Za-z0-9_]+', name), 'Literals must be alphanumeric or underscore.'
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
        assert re.match('[A-Za-z0-9_]+', name), 'Variables must be alphanumeric or underscore.'
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
    return Statement.state(statementOrExpression).statement

class PythonVar:
    def __init__(self, methodName, varName):
        self.methodName = methodName
        self.varName = varName
    def __str__(self):
        return self.varName + " from " + self.methodName
    
class Statement:
    # All Statements, mapped by "generic" Expression representation.
    statements = dict()

    ProofCount = 0 # counter to number each proof
    utilizedProofNumbers = set() #  don't remove from _assumptionSetsForWhichProven of a ProofStepInfo unless it's proofnumber is not utilized
    
    def __init__(self, genericExpression):
        '''
        Do not use the Statement constructor externally.  Instead, do so indirectly;
        via the state method of an Expression or other Expression methods that
        generate new Statements from old Statements.
        '''
        # this is the generic expression, with instance variables replaced by indices
        self._genericExpression = genericExpression
        genericExpression.statement = self
        # set of Expressions this Statement is known to represent (instance variables may have different labels)
        self._manifestations = {genericExpression}
        # The default manifestation will be the first Expression represented by this Statement that was stated 
        self._defaultManifestation = None
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
#        self._proofStepInfo = Statement.ProofStepInfo(self) # information regarding proofs for various assumption sets
        self._registeredVar = None # variable name that refers to this statement and is registered
        self._registeredContext = None # Context for the registration
        self.proofNumber = float("inf") # number each proof for statements proven with no assumptions necessary
        self._prover = None # a Prover that proves this statement if it has no free variables and has been proven (theorem)

    @staticmethod
    def state(expression):
        '''
        Make a Statement from the given Expression.  All of its instance variables 
        will be replaced with generic indices for storage in the statements database, 
        equating statements that differ only by instance variable labels.  The original 
        expression will be returned, but will be linked with its corresponding statement.
        '''
        from booleans import IMPLIES
        if isinstance(expression, Operation) and expression.operator == IMPLIES and len(expression.operands) == 2:
            # When stating an Implication, link the consequence to the
            # condition as an implicating Statement.
            implication = Statement._makeStatement(expression)
            hypothesis = Statement.state(expression.operands[0]).statement
            conclusion = Statement.state(expression.operands[1]).statement
            conclusion.addImplicator(hypothesis, implication)
        else:
            Statement._makeStatement(expression)
        return expression

    @staticmethod
    def _makeStatement(expression):
        # find/add the statement and return it.
        varAssignments = []
        genericExpression = expression.makeGeneric(varAssignments)
        rep = repr(genericExpression)
        statement = Statement.statements.setdefault(rep, Statement(genericExpression))
        statement._manifestations.add(expression)
        if statement._defaultManifestation == None:
            statement._defaultManifestation = expression
        expression.statement = statement
        return statement             
             
    def __str__(self):
        return str(self.getExpression())
    
    def _register(self, context, varName):
        """
        Register the statement to a given Context and variable name.  Called by Context.register(..).
        """
        assert(isinstance(context, Context))
        assert len(self.freeVars()) == 0, 'May only register statements with no free variables (a potential theorem)'
        if not self.wasProven():
            print 'Warning: registering an unproven theorem,', varName, "of", context.name
        if self._registeredVar != None and self._registeredVar != varName:
            print 'Warning: overwriting theorem registration,', self._registeredVar, "of", self._registeredContext.name, 'now', varName, "of", context.name
        self._registeredContext = context
        self._registeredVar = varName
        
    def getRegisteredVar(self):
        """
        Returns the PythonVar identifying the variable for which this 
        Statement has been registered, or None if no variable has been registered to it.
        """
        return self._registeredVar
    
    def getRegisteredContext(self):
        return self._registeredContext
        
    def getContexts(self):
        return list(self._contexts)
        
    def getManifestations(self):
        '''
        The set of Expressions that are represented by this Statement
        (may differ only in the labeling of instance Variables).
        '''
        return self._manifestations
        
    def getExpression(self):
        '''
        The default Expression represented by this Statement (the first one stated).
        '''
        return self._defaultManifestation
    
    def freeVars(self):
        return self.getExpression().freeVars()
    
    def addContext(self, context):
        self._contexts.add(context)

    @staticmethod
    def specialize(originalExpr, subMap):
        '''
        State and return a tuple of (specialization, conditions).  The 
        specialization derives from the given original statement and its conditions
        via a specialization inference rule.  It is the specialized form of the 'original' 
        expression by substituting one or more instance variables of outer Forall operations 
        according to the given substitution map.  It may have free variables which can be 
        considered to be "arbitrary" variables used in logical reasoning.  Eventually
        they should be bound again via generalization (the counterpart to specialization).
        '''
        from booleans import FORALL
        subMap = SubstitutionMap(subMap)
        substitutingVars = set(subMap.getSubstitutingVars())
        instanceVars = set()
        conditions = set()
        expr = originalExpr
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
        specializedExpr = Statement.state(expr.substituted(nonRelabSubMap, relabelMap = relabMap))
        mappedConditions = {asStatement(condition.substituted(subMap)) for condition in conditions}
        Statement.state(originalExpr)
        specializedExpr.statement.addSpecializer(originalExpr.statement, subMap, mappedConditions)
        return specializedExpr, mappedConditions
                       
    @staticmethod
    def generalize(originalExpr, newForallVars, newConditions=None):
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
        from booleans import Forall
        generalizedExpr = Statement.state(Forall(newForallVars, originalExpr, newConditions))
        # In order to be a valid tautology, we simply have to make sure that the expression is zero or more
        # nested Forall operations with the original as the inner instanceExpression.
        Statement.state(originalExpr)
        generalizedExpr.statement.addGeneralizer(originalExpr.statement, newForallVars, newConditions)
        Statement._checkForallInstanceExpr(generalizedExpr, originalExpr)
        return generalizedExpr
    
    @staticmethod
    def _checkForallInstanceExpr(expr, instanceExpr):
        '''
        Make sure the expr contains the instanceExpr in zero or more nested Forall operations.
        '''
        from booleans import FORALL
        while expr != instanceExpr:
            assert isinstance(expr, OperationOverInstances) and expr.operator == FORALL
            expr = expr.instanceExpression
                
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
        self._specializers.add((original, subMap.makeImmutableForm(), tuple(conditions)))
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
                generalityProver = Statement.Prover(original, self.assumptions - set(conditions), self, "specialization")
                corequisites = [generalityProver] + [Statement.Prover(condition, self.assumptions, self, "specialization condition") for condition in conditions]
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
            if stmt._hypothesisOfImplication != None:
                hypothesis = stmt._hypothesisOfImplication
                breadth1stQueue.append(Statement.Prover(stmt._conclusionOfImplication, self.assumptions | {hypothesis}, self, "hypothetical reasoning"))

    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True, qedProof=False):
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
                print "tmpProvers", len(Statement.Prover._tmpProvers)
                print "proven at depth", prover.depth
                if markProof:
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
    # All contexts, mapped by name
    contexts = dict()

    def __init__(self, name):
        # map "unique" internal expression representations to corresponding statements
        # which can map to one or more equivalent expressions (that may have different
        # external representations)
        self.literals = dict()
        assert re.match('[A-Z][A-Z0-9_]*', name), 'Context names must be alphanumeric or underscore, starting with a alphabet character, and with only capitalized alphabet characters.'
        self.name = name
        Context.contexts[name] = self
        self._onDemandDerivations = dict()
        self._onDemandNames = list() # in the order they were added
        self._axiomsDictFn = None
        self._registeredStmts = dict()

    def __repr__(self):
        return self.name
    
    def register(self, name, index=None):
        '''
        Register the statement that is an attribute of this Context with the given name.
        The statement will thence refer to this Context and variable name.  If index
        is provided then this refers to an element of a list attribute.
        '''
        if index == None:
            self.__dict__[name].statement._register(self, name)
            self._registeredStmts[name] = self.__dict__[name]
        else:
            nameWithIndex = name + '[' + str(index) + ']'
            self.__dict__[name][index].statement._register(self, nameWithIndex)
            self._registeredStmts[nameWithIndex] = self.__dict__[name][index]
    
    def axiomsOnDemand(self, axiomsDictFn):
        '''
        The first time an axiom or theorem attribute is accessed, execute
        the axiomsDictFn and set the resulting axioms as attributes.  These
        will automatically be registered (see the register method).
        '''
        self._axiomsDictFn = axiomsDictFn
    
    def deriveOnDemand(self, name, derivationFn):
        '''
        When the attribute of the given name is accessed, it will
        be set to the result of the derivationFn.  This will automatically
        be registered after being derived (see the register method).
        '''
        self._onDemandDerivations[name] = derivationFn
        self._onDemandNames.append(name)
    
    def _doDerivation(self, name):
        if not name in self._onDemandDerivations:
            return
        storedTmpProvers = dict(Statement.Prover._tmpProvers)
        self.__dict__[name] = self._onDemandDerivations.pop(name)()
        self.register(name)
        Statement.Prover._tmpProvers = storedTmpProvers
        
    def __getattr__(self, name):
        '''
        When accessing a "deriveOnDemand" attribute, the Derivation's
        function is executed and the attribute is assigned the result.
        '''
        if name.startswith('__'): 
            raise AttributeError # skip special Python attributes
        if self._axiomsDictFn != None:
            axiomsDict = self._axiomsDictFn()
            for axiomName, axiom in axiomsDict.iteritems():
                self.__dict__[axiomName] = self.stateAxiom(axiom)
                self.register(axiomName)
            self._axiomsDictFn = None
        self._doDerivation(name)
        if not name in self.__dict__:
            raise AttributeError
        return self.__dict__[name]
    
    def deriveAll(self):
        for name in self._onDemandNames:
            self._doDerivation(name)

    def addLiteral(self, name=None, formatMap=None, literal=None):
        if literal != None:
            assert literal.context == self
            assert name == None or name == literal.name
            assert formatMap == None
            self.literals[literal.name] = literal
            return literal
        elif not name in self.literals:
            self.literals[name] = Literal(name, self, formatMap)
        return self.literals[name]
    
    def getLiteral(self, name):
        return self.literals[name]

    def stateAxiom(self, expression):
        '''
        Make a Statement in the same way as the state(..) function, but also set its
        axiom flag.  An axiom may not have any free variables.
        '''
        freeVars = expression.freeVars()
        assert len(freeVars) == 0, 'Expressions with free variable may not be converted to a statement (bind with an OperationOverInstances): ' + str(freeVars)
        statement = Statement.state(expression).statement
        statement.makeAxiom()
        return expression


'''
def registerTheorems(moduleName, variables):
    for vName, v in variables.iteritems():
        if isinstance(v, Expression) and v.statement != None and len(v.freeVars()) == 0:
            v.statement.registerPythonVar(PythonVar(moduleName, vName))
'''