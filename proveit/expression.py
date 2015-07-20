"""
This is the statement module.
"""

import re
from sre_constants import LITERAL

STRING = 1
MATHML = 2
LATEX = 3

class Expression:
    lastCreationNum = 0
    
    def __init__(self, formatMap=None):
        # Will be the associated Statement if the Expression is
        # ever 'stated' in a particular prover.
        self.statement = None
        self.formatMap = formatMap
        Expression.lastCreationNum += 1
        self.creationNum = Expression.lastCreationNum
        
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
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        assert self.isProven(assumptions)==True, "Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions)
        return self
    
    def check(self, assumptions=frozenset()):
        """
        Check that this statement is true under the given assumptions but not for a step
        of a theorem proof (that is, temporary provers aren't stored).
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        assert self.isProven(assumptions, markProof=False)==True, "Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions)
        return self
        
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.
        """
        if self.statement == None: Statement.state(self)
        assert isinstance(self.statement, Statement)
        return self.statement.isProven(assumptions, maxDepth, markProof)
    
    def wasProven(self, assumptions=frozenset()):
        """
        Returns True iff this statement has already be proven under the given assumptions.
        """
        if self.statement == None:
            return False
        else:
            assert isinstance(self.statement, Statement)            
            return self.statement.wasProven(assumptions)
        
    def substituted(self, varMap, operationMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to varMap (Variable:Expression dictionary) and/or operations
        with variable operators substituted according to operationMap
        (Variable:Lambda dictionary) and/or relabeled according to  
        relabelMap (Variable:Variable dictionary).
        If supplied, reservedVars is a dictionary that maps reserved Variable's
        to relabeling exceptions.  You cannot substitute with an expression that
        uses a restricted variable and you can only relabel the exception to the
        restricted variable.  This is used to protect an Lambda function's "scope".
        '''
        return self
    
    def relabeled(self, relabelMap, reservedVars=None):
        '''
        A watered down version of substitution in which only variable labels are
        changed.  This may also involve substituting a MultiVariable with a list
        of Variables.
        '''
        return self.substituted(varSubMap=dict(), operationSubMap=dict(), relabelMap=relabelMap, reservedVars=reservedVars)
    
    def _validateRelabelMap(self, relabelMap):
        assert len(relabelMap) == len(set(relabelMap.values())), "Cannot relabel different Variables to the same Variable."
            
    """        
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        return self
    """
    
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
        if subMap is None: subMap = dict()
        (specialization, conditions) = Statement.specialize(self, subMap)
        return specialization.check({self} | conditions)
        
    def generalize(self, newForallVars, newConditions=None):
        if len(newForallVars) == 0 and newConditions is None:
            return self # trivial case
        return Statement.generalize(self, newForallVars, newConditions) #.check({self})
    
    """
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
    """
    
    def proveByEval(self):
        '''
        Prove self by calling self.evaluate() if it equates the expression to TRUE.
        The evaluate method must be implemented by the derived class.
        '''
        return self.evaluate().deriveViaBooleanEquality().prove()
    
    def _restrictionChecked(self, subbedExpr, reservedVars):
        '''
        Check that the substituted expression does not use any reserved variables
        (arguments of a Lambda function Expression).
        '''
        if not reservedVars is None and not subbedExpr.freeVars().isdisjoint(reservedVars.keys()):
            print "substituted free variables", subbedExpr.freeVars()
            print "reserved variables", reservedVars.keys()
            raise ValueError("Must not make substitution with reserved variables  (i.e., arguments of a Lambda function)")
        return subbedExpr
    
    def __len__(self):
        '''
        A singular Expression has length of 1.  An ExpressionList has a length that
        is the number of Expressions in the list.
        '''
        return 1
    
    def __iter__(self):
        '''
        Iterating over a singular Expression just yields the Expression itself.
        Iterating over an ExpressionList will iterate over each Expression in the list.
        '''
        yield self
        
    def first(self):
        '''
        The "first" item of a singular Expression is itself.  For an ExpressionList, it is
        the first Expression in the list.
        '''
        return self

class ExpressionList(Expression):
    """
    An ExpressionList is a composite Expression composed of an ordered list of member
    Expression's.  It can play different roles depending upon where it is used:
    operandS of an Operation, argumentS or conditionS or expressionS of a Lambda expression
    (the capitolized 'S' here signifies the role of the ExpressionList to make multiple
    sub-expressions in one).
    An ExpressionList is always flattened and never nested.  To represent a list of lists
    type expression, they must be explicitly nested as Operations.
    """
    def __init__(self, *expressions):
        '''
        Initialize an ExpressionList from one or more Expression arguments.  When
        this includes any ExpressionList arguments, they flattened by expanding the
        sub-expressions.
        '''
        if len(expressions) == 1:
            # this allows one to pass an explicit list/tuple to the ExpressionList constructor 
            # as a single argument rather than a list of arguments.
            expressions = tuple(expressions[0]) 
        for expr in expressions:
            if not isinstance(expr, Expression):
                raise TypeError('ExpressionList must be created out of Expressions')
        def genSubExpr(expr):
            if isinstance(expr, ExpressionList):
                for subExpr in expr.expressions: yield subExpr
            else: yield expr
        self.expressions = tuple(sum([[subExpr for subExpr in genSubExpr(expr)] for expr in expressions], []))
    
    def __repr__(self):
        return ','.join([repr(expr) for expr in self.expressions])
    
    def formatted(self, formatType, fenced=False):
        outStr = ''
        if len(self.expressions) == 0: fenced = True # for an empty list, show the parenthesis to show something.
        if formatType == STRING or formatType == LATEX:
            if fenced: outStr += '('
            outStr += ','.join([expr.formatted(formatType) for expr in self.expressions])
            if fenced: outStr += ')'
        elif formatType == MATHML:
            if fenced: outStr += '<mfenced>'
            else: outStr += '<mfenced open="" close="">'
            outStr += ''.join([expr.formatted(formatType) for expr in self.expressions])
            outStr += '</mfenced>'
        return outStr
    
    def __getitem__(self, index):
        '''
        Returns the sub-Expression of the given index.
        '''
        return self.expressions[index]
    
    def __iter__(self):
        '''
        Returns the sub-Expression iterator.
        '''
        return self.expressions.__iter__()
    
    def __len__(self):
        '''
        Returns the number of sub-Expressions.
        '''
        return len(self.expressions)
    
    def first(self):
        '''
        Returns the first Expression in the list.
        '''
        return self.expressions[0]

    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        return ExpressionList([expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars) for expr in self.expressions])
                
    """
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        return ExpressionList([expr.makeGeneric(varAssignments, varMap) for expr in self.expressions])
    """
        
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.expressions])
        
    def freeVars(self):
        '''
        Returns the union of the free Variable sof the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.expressions])

def _expressionOrList(expressions):
    '''
    From one or more expressions, return the flattened ExpressionList or single Expression.
    '''
    expressionList = ExpressionList(*expressions)
    return expressionList.first() if len(expressionList) == 1 else expressionList
        
class Literal(Expression):
    """
    A Literal expresses contextual meaning and they are not interchangeable.
    """
    def __init__(self, name, formatMap = None):
        Expression.__init__(self, formatMap)
        assert re.match('[A-Za-z0-9_]+', name), 'Literals must be alphanumeric or underscore.'
        self.name = name
        self.context = None
        
    def setContext(self, context):
        assert(self.context is None or self.context == context), "Cannot change the Context of a Literal once it has been set"
        self.context = context
    
    def __repr__(self):
        return '\\' + repr(self.context) + '.' + self.name
    
    def formatted(self, formatType, fenced=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING or formatType == LATEX:
            return self.name
        elif formatType == MATHML:
            return '<mi>' + self.name + '</mi>'

class Literals(dict):
    """
    A dictionary mapping names to Literals.
    """
    def __init__(self):
        dict.__init__(self)
    
    def add(self, literalOrName=None, formatMap=None):
        '''
        Create/add Literal to the Literals dictionary and return it.
        '''
        if not isinstance(literalOrName, Literal):
            name = literalOrName
            literal = Literal(literalOrName, formatMap)
        else:
            literal = literalOrName
            name = literal.name
        assert not name in self, "Duplicate Literal name: " + str(name)
        self[name] = literal
        return literal

class Variable(Expression):
    """
    A Variable is an interchangeable label.  They may be relabeled Variable to Variable.
    Through specialization of a Forall statement over one or more Variables, those Variables
    may each be substituted with a general Expression.
    """    
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
        if formatType == STRING or formatType == LATEX:
            return self.name
        elif formatType == MATHML:
            return '<mi>' + self.name + '</mi>'
    
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        if (varSubMap != None) and (self in varSubMap):
            sub = varSubMap[self]
            if not isinstance(sub, Expression):
                raise TypeError('Must substitute a Variable with an Expression')                
            if isinstance(sub, ExpressionList):
                raise TypeError('May not substitute a Variable with an ExpressionList.  Only MultiVariables may be substituted with an ExpressionList.') 
            return self._restrictionChecked(sub, reservedVars)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)            
            if not isinstance(subbed, Variable):
                raise TypeError('May only relabel Variable to Variable')
            if isinstance(subbed, MultiVariable):
                raise TypeError('May not relabel a Variable to a MultiVariable')
            if reservedVars != None and subbed in reservedVars.keys():
                assert self == reservedVars[subbed], "Relabeling in violation of Variable restriction."
            return subbed
        return self
                
    """
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
    """
        
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

class MultiVariable(Variable):
    '''
    A MultiVariable is a stand-in for any number (zero or more) of Variables as Lambda 
    arguments or Operation operands.  They may be relabeled MultiVariable to MultiVariable.
    Through statement specialization, they may be substituted with a list of Variables in any
    scope (Lambda expressions define scopes).
    '''
    def __init__(self, name, formatMap = None):
        Variable.__init__(self, name, formatMap)
        self.name = name
        
    def __repr__(self):
        return '\\' + self.name + '*'

    def formatted(self, formatType, fenced=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING:
            return self.name + '**'
        elif formatType == LATEX:
            return self.name + '^{**}'
        elif formatType == MATHML:
            return '<msup><mi>' + self.name + '</mi><mo>**</mo></msup>'
    
    def _substitutedGenerator(self, varSubMap, relabelMap = None, reservedVars = None):
        '''
        Yield the substitution of this MultiVariable according to subMap
        and/or relabeled according to relabelMap.
        '''
        if (varSubMap != None) and (self in varSubMap):
            substitutionList = ExpressionList(varSubMap[self]).expressions
            for expr in substitutionList:
                if not isinstance(expr, Expression): raise TypeError('Must substitute with an Expression or list of Expressions')
                yield self._restrictionChecked(expr, reservedVars)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)            
            for subVar in subbed:
                if not isinstance(subVar, Variable):
                    raise TypeError('Must relabel a MultiVariable with a MultiVariable or list of Variables')
                if reservedVars != None and subVar in reservedVars.keys():
                    assert self == reservedVars[subVar], "Relabeling in violation of Variable restriction."
                yield subVar
        else:
            yield self
    
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Return this expression with the MultiVariable substituted 
        according to subMap and/or relabeled according to relabelMap.
        May expand to an ExpressionList.
        '''
        return _expressionOrList([expr for expr in self._substitutedGenerator(varSubMap, relabelMap, reservedVars)])
        
    """
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap != None and self in varMap:
            subbed = varMap[self]
            assert isinstance(subbed, MultiVariable), "May only relabel MultiVariable to MultiVariable"
            return subbed
        return self
    """
    
    def usedVars(self):
        return {self}
        
    def freeVars(self):
        return {self}    

class MultiIndexVariable(MultiVariable):
    def __init__(self, n):
        MultiVariable.__init__(self, '_' + str(n) + '_')
    
class Operation(Expression):
    # Register makers for specific Operator Literals to create an Object of the derived
    # class rather than the generic Operation base class when created.
    _registeredMakers = dict()
    
    # The Forall and Implies operations are special and must be registered once and only once
    _ForallLiteral = None
    _ImpliesLiteral = None
    
    @staticmethod
    def registerOperation(operatorLabel, maker):
        assert isinstance(operatorLabel, Literal)
        Operation._registeredMakers[operatorLabel] = maker
        if operatorLabel.name.upper() == 'FORALL':
            assert Operation._ForallLiteral is None or Operation._ForallLiteral == operatorLabel, "May only register one Forall Operation"
            Operation._ForallLiteral = operatorLabel
        if operatorLabel.name.upper() == 'IMPLIES':
            assert Operation._ImpliesLiteral is None or Operation._ImpliesLiteral == operatorLabel, "May only register one Implies Operation"
            Operation._ImpliesLiteral = operatorLabel

    @staticmethod
    def make(operator, operand):
        if operator in Operation._registeredMakers:
            # if it is registered, use the registered "maker"
            operation = Operation._registeredMakers[operator](operand)
            assert isinstance(operation, Operation), 'Registered Operation maker must make an Operation type'
            assert operation.operator == operator, 'Registered Operation maker function must make an Operation true to its given operator: ' + str(operator)
            assert operation.operand == operand, 'Registered Operation maker function must make an Operation true to its given operand.  Operator: ' + str(operator) + '; Operand: ' + str(operand)
            return operation
        return Operation(operator, operand)
    
    @staticmethod
    def _forallLiteral():
        assert not Operation._ForallLiteral is None, "Must register a Forall Operation before specializing or generalizing a Statement"
        return Operation._ForallLiteral

    @staticmethod
    def _forallMaker():
        forallLiteral = Operation._forallLiteral()
        return Operation._registeredMakers[forallLiteral]

    @staticmethod
    def _impliesLiteral():
        assert not Operation._ImpliesLiteral is None, "Must register a Implies operation before stating an implication"
        return Operation._ImpliesLiteral

    @staticmethod
    def _impliesMaker():
        impliesLiteral = Operation._impliesLiteral()
        return Operation._registeredMakers[impliesLiteral]
    
    def __init__(self, operator, operands):
        '''
        Create an operation with the given operator and operand(s).  The operator can be a 
        Literal, Variable, or Lambda function.  The operand(s) may be singular or plural (iterable).
        '''
        Expression.__init__(self)
        if not (isinstance(operator, Literal) or isinstance(operator, Variable) or isinstance(operator, Lambda)):
            raise TypeError('operator must be a Literal, Variable, or a Lambda function')
        self.operator = operator
        self.operand = _expressionOrList(operands)
        assert isinstance(self.operand, Expression)
        if isinstance(operator, Lambda):
            if len(self.operand) != len(operator.argument):
                raise ValueError("Number of arguments and number of operands must match.")

    def __repr__(self):
        return repr(self.operator) + '(' + repr(self.operand) +')'
    
    def formattedOperator(self, formatType):
        # override this default as desired
        return self.operator.formatted(formatType, fenced=True)
    
    def formatted(self, formatType, fenced=False):
        # override this default as desired
        if formatType == STRING or formatType == LATEX:
            return self.formattedOperator(formatType) +  '(' + self.operand.formatted(formatType) + ')'
        elif formatType == MATHML:
            outStr = '<mrow>' + self.formattedOperator(formatType) + '<mfenced>'
            outStr += self.operand.formatted(formatType)
            outStr += '</mfenced></mrow>'
            return outStr
        
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        operator = self.operator
        subbedOperand = self.operand.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
        if not operationSubMap is None and isinstance(operator, Variable) and operator in operationSubMap:
            # Substitute the entire operation(s) via Lambda expression(s)
            operatorSubs = [operationSubMap[operator]]
            if isinstance(self.operator, MultiVariable):
                # A MultiVariable operator may be substituted by an ExpressionList of 
                # multiple operator substitutions resulting in a list of operations for the substitution.
                operatorSubs = ExpressionList(operationSubMap[operator]) 
            subbedOperations = []
            for operatorSub in operatorSubs:
                if not isinstance(operatorSub, Lambda):
                    raise TypeError("Operation substitution requires a Lambda function to define the new operation.")
                # Substitute the entire operation via a lambda expression
                # For example, f(x, y) -> x + y.
                if len(subbedOperand) != len(operatorSub.argument):
                    raise ValueError('Cannot substitute an Operation with the wrong number of arguments')
                operandSubMap = {argument:operand for argument, operand in zip(operatorSub.argument, subbedOperand)}
                if not reservedVars is None:
                    # the reserved variables of the lambda expression excludes the lambda arguments
                    # (i.e., the arguments mask externally reserved variables).
                    lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if k not in operatorSub.argument}
                else: lambdaExprReservedVars = None
                subbedOperations.append(self._restrictionChecked(operatorSub.expression, lambdaExprReservedVars).substituted(operandSubMap, None))
            return _expressionOrList(subbedOperations)
        else:
            # Can perform substitutions within the Operator 
            subbedOperator = self.operator.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
            if isinstance(subbedOperator, ExpressionList):
                # must have substituted an ExpressionList for a MultiVariable operator
                return _expressionOrList([Operation.make(operator, subbedOperand) for operator in subbedOperator])
            return Operation.make(subbedOperator, subbedOperand)
            
    """
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap == None:
            varMap = dict()
        genericOperator = self.operator.makeGeneric(varAssignments, varMap)
        genericOperand = self.operand.makeGeneric(varAssignments, varMap)
        return Operation.make(genericOperator, genericOperand)
    """
        
    def usedVars(self):
        '''
        Returns the union of the operator and operand used variables.
        '''
        return self.operator.usedVars().union(self.operand.usedVars())
        
    def freeVars(self):
        '''
        Returns the union of the operator and operand free variables.
        '''
        return self.operator.freeVars().union(self.operand.freeVars())

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps an argument to
    an expression.  The argument is a Variable in the expression or an
    ExpressionList of Variables in the expression.  For example,
    (x, y) -> sin(x^2 + y).
    Optionally, it also has a domain condition that determine when the arguments
    are in the valid domain of the map.  If the domain condition is an
    ExpressionList, all conditions must be true for the conditions to be satisfied.
    '''
    def __init__(self, arguments, expressions, domainConditions=None):
        '''
        Initialize a Lambda expression given an argument(s), expression(s), and optional domainCondition(s).
        These may be singular or plural (iterable).
        '''
        self.argument = _expressionOrList(arguments)
        for var in self.argument:
            if not isinstance(var, Variable): 
                raise TypeError('Lambda argument must be a Variable or an ExpressionList of Variables')
        if len(set(self.argument)) != len(self.argument):
            raise ValueError('Lambda arguments must be unique with respect to each other.')
        self.expression = _expressionOrList(expressions)
        hasNoConditions = domainConditions is None or len(domainConditions) == 0
        self.domainCondition = ExpressionList() if hasNoConditions else _expressionOrList(domainConditions)
        if not isinstance(self.expression, Expression):
            raise TypeError("A Lambda expression must have Expression type")
        if not isinstance(self.domainCondition, Expression):
            raise TypeError("A Lambda domainCondition must have Expression type")
    
    def hasCondition(self):
        '''
        Returns true if this Lambda Expression has a domain condition.
        '''
        return len(self.domainCondition) > 0
    
    def __repr__(self):
        repStr = '[(' + ','.join(repr(var) for var in self.argument) + ')->' + repr(self.expression)
        if self.hasCondition():
            repStr += '|' +  repr(self.domainCondition)
        repStr += ']'
        return repStr
    
    def formatted(self, formatType, fenced=False):
        '''
        The default Lambda formatting is of the form "(x, y) -> f(x, y)".
        '''
        if formatType == STRING:
            outStr = '[' if fenced else ''
            outStr += '(' + ', '.join([var.formatted(formatType) for var in self.argument])
            if self.hasCondition():
                outStr += '|' + self.domainCondition.formatted(formatType)
            outStr += ') -> ' + self.expression.formatted(formatType)
            if fenced: outStr += ']'
        elif formatType == LATEX:
            outStr = r'\left[' if fenced else ''
            outStr += r'\left(' + ', '.join([var.formatted(formatType) for var in self.argument])
            if self.hasCondition():
                outStr += '|' + self.domainCondition.formatted(formatType)
            outStr += r'\right) \rightarrow ' + self.expression.formatted(formatType)
            if fenced: outStr += r'\right]'
        elif formatType == MATHML:
            outStr = "<mfenced open='[' close=']'>" if fenced else ''
            if self.hasCondition():
                outStr += "<mfenced open='[' close=']'>"
            outStr += '<mrow><mfenced>'
            for var in self.argument:
                outStr += var.formatted(formatType)
            outStr += '</mfenced>'
            if self.hasCondition():
                outStr += '<mo>&#x2223;</mo><mfenced open="{" close="}">'
                outStr += self.domainCondition.formatted(formatType)
                outStr += '</mfenced></mfenced>'
            outStr += '<mo>&#x21A6;</mo>'
            outStr += self.expression.formatted(formatType, fenced=True)
            outStr += '</mrow>'
            if fenced: outStr += '</mfenced>'
        return outStr
        
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Return this expression with its variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        The Lambda argument(s) have their own scope within the Lambda 
        expression or domainCondition and do not get substituted.  They may be
        relabeled, however.  Substitutions within the Lambda expression are 
        restricted to exclude the Lambda argument(s) themselves (these Variables 
        are reserved), consistent with any relabeling.
        '''
        # Can't substitute the lambda argument variables; they are in a new scope.
        lambdaArgSet = set(self.argument)
        innerVarSubMap = {key:value for (key, value) in varSubMap.iteritems() if key not in lambdaArgSet}
        if operationSubMap is None: operationSubMap = dict()
        innerOperationSubMap = {key:value for (key, value) in operationSubMap.iteritems() if key not in lambdaArgSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        newArgs = []
        for arg in self.argument:
            newArg = arg.relabeled(relabelMap, reservedVars)
            newArgs += list(newArg)
            # Here we enable an exception of relabeling to a reserved variable as
            # long as we are relabeling the Lambda argument and internal variable together.
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            # Also works with MultiVariables: (x, y*) -> f(x, y*) relabeled to (x, y, z) -> f(x, y, z).
            for x in newArg: innerReservations[x] = arg
        # the lambda expression with the substitution:
        subbedExpr = self.expression.substituted(innerVarSubMap, innerOperationSubMap, relabelMap, innerReservations)
        if self.hasCondition():
            subbedCondition = self.domainCondition.substituted(innerVarSubMap, innerOperationSubMap, relabelMap, innerReservations)
        else: subbedCondition = None
        return Lambda(newArgs, subbedExpr, subbedCondition)

    """
    def makeGeneric(self, varAssignments, varMap = None):
        '''
        A generic relabeling in which bound variables are replaced with indices in the
        order they appear.
        '''
        if varMap == None:
            varMap = dict()
        genericVariables = []
        for var in self.argument:
            varAssignments.append(var)
            if isinstance(var, MultiVariable):
                varMap[var] = MultiIndexVariable(len(varAssignments))                
            else:
                varMap[var] = IndexVariable(len(varAssignments))
            genericVariables.append(varMap[var])
        genericExpression = self.expression.makeGeneric(varAssignments, varMap)
        if self.hasCondition():
            genericCondition = self.domainCondition.makeGeneric(varAssignments, varMap)
        else: genericCondition = None
        return Lambda(genericVariables, genericExpression, genericCondition)
    """
        
    def usedVars(self):
        '''
        The used variables the lambda function are the used variables of the expression
        plus the lambda argument variables.
        '''
        usedVs = self.expression.usedVars().union(set(self.argument))
        if self.hasCondition():
            for condition in self.domainCondition:
                usedVs |= condition.usedVars()
        return usedVs
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the expression
        minus the lambda argument variables.  The lambda function binds those variables.
        '''
        innerFreeVs = set(self.expression.freeVars())
        if self.hasCondition():
            for condition in self.domainCondition:
                innerFreeVs |= condition.freeVars()
        return innerFreeVs - set(self.argument)    
            
def asStatement(statementOrExpression):
    '''
    Given an expression, returns the corresponding statement (made in the current prover).
    Given a statement, returns what was given.
    '''
    if isinstance(statementOrExpression, Statement):
        return statementOrExpression
    return Statement.state(statementOrExpression).statement

class Statement:
    # All Statements, mapped by "generic" Expression representation.
    statements = dict()

    ProofCount = 0 # counter to number each proof
    utilizedProofNumbers = set() #  don't remove from _assumptionSetsForWhichProven of a ProofStepInfo unless it's proofnumber is not utilized
    
    def __init__(self, expression, _context=None, _name=None, _isAxiom=False, _isNamedTheorem=False):
        '''
        Do not use the Statement constructor externally.  Instead, do so indirectly;
        via the state method of an Expression or other Expression methods that
        generate new Statements from old Statements.
        '''
        self._expression = expression
        self._context = _context
        self._name = _name
        self._hypothesisOfImplication = None
        self._conclusionOfImplication = None
        self._implicationsOfHypothesis = set()
        self._implicators = set()
        self._specializers = set()
        self._generalizers = set()
        self._specializations = set()
        self._generalizations = set()
        self._isAxiom = _isAxiom
        self._isNamedTheorem = _isNamedTheorem
        self.proofNumber = float("inf") # number each proof for statements proven with no assumptions necessary
        self._prover = None # a Prover that proves this statement if it has no free variables and has been proven (theorem)

    @staticmethod
    def state(expression, _context=None, _name=None, _isAxiom=False, _isNamedTheorem=False):
        '''
        Make a Statement from the given Expression and return the Expression.
        '''
        from prover import Prover
        
        statement = Statement(expression, _context, _name)
        statement = Statement.statements.setdefault(repr(expression), statement)
        expression.statement = statement
        
        if _isAxiom:
            assert expression in _context._axioms, "An axiom statement must be made properly in its context"
        if _isNamedTheorem:
            assert expression in _context._theorems, "A theorem statement must be made properly in its context"
        if not _context is None:
            statement._isAxiom = _isAxiom
            statement._isNamedTheorem = _isNamedTheorem
        
        if _isAxiom or _isNamedTheorem:
            # Mark as proven up to axioms and theorems. The proof won't be really complete until required
            # theorems are completely proven, but the proof steps will be in place in any case. 
            Prover._markAsProven(statement, Prover(statement, []))
            
        # When stating an implication, link together the implication, hypothesis and conclusion
        if isinstance(expression, Operation) and expression.operator == Operation._impliesLiteral() and len(expression.operand) == 2:
            implication = statement
            hypothesis = Statement.state(expression.operand[0]).statement
            conclusion = Statement.state(expression.operand[1]).statement
            conclusion.addImplicator(hypothesis, implication)
        
        expression.statement = statement
        return expression
            
    """
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
    """
             
    def __str__(self):
        return str(self.getExpression())    
        
    """
    def getManifestations(self):
        '''
        The set of Expressions that are represented by this Statement
        (may differ only in the labeling of instance Variables).
        '''
        return self._manifestations
    """
        
    """
    def getExpression(self):
        '''
        The default Expression represented by this Statement (the first one stated).
        '''
        return self._defaultManifestation
    """
    
    def getExpression(self):
        return self._expression
    
    def freeVars(self):
        return self.getExpression().freeVars()
    
    @staticmethod
    def specialize(originalExpr, subMap):
        '''
        State and return a tuple of (specialization, conditions).  The 
        specialization derives from the given original statement and its conditions
        via a specialization inference rule.  It is the specialized form of the 'original' 
        expression by substituting one or more instance variables of outer Forall operations 
        according to the given substitution map.  Remaining variables in the map may
        be included for simultaneous relabelling.  There may end up being free variables
        which can be considered to be "arbitrary" variables used in logical reasoning.  
        Eventually they should be bound again via generalization (the counterpart to 
        specialization).
        '''
        substitutingVars = set()
        operationSubMap = dict()
        # the k==v cases are implicit, so remove them
        subMap = {k:v for k, v in subMap.iteritems() if k != v}
        for subVar in subMap.keys():
            if isinstance(subVar, Operation): 
                operation = subVar
                subVar = operation.operator
                operationSubMap[subVar] = Lambda(operation.operand, _expressionOrList(subMap[operation]))
            if not isinstance(subVar, Variable):
                raise TypeError("Substitution map must map either Variable types or Operations with Variable operators")
            substitutingVars.add(subVar)
        varSubMap = {var:_expressionOrList(expr) for var, expr in subMap.iteritems() if isinstance(var, Variable)}
        FORALL = Operation._forallLiteral()
        assert originalExpr.operator == FORALL, "May only specialize a FORALL expression"
        assert isinstance(originalExpr.operand, Lambda), "FORALL expression must have 1 Lambda operand"
        # extract the forall expression and instance variables from the lambda expression operand
        lambdaExpr = originalExpr.operand
        expr, instanceVars = lambdaExpr.expression, set(lambdaExpr.argument)
        # the condition over which the forall is restricted is determined by the domain of the lambda expression operand
        conditions = lambdaExpr.domainCondition if lambdaExpr.hasCondition() else tuple()
        # any remaining variables may be used only for relabeling
        relabelVars = substitutingVars.difference(instanceVars)
        for relabelVar in relabelVars:
            if relabelVar in operationSubMap:
                raise ValueError('May only perform Operation specialization by substituting instance variables of forall operations')
            if isinstance(relabelVar, MultiVariable):
                for v in varSubMap[relabelVar]:
                    if not isinstance(v, Variable):
                        raise ValueError('May only specialize by substituting instance variables of forall operations or otherwise simply relabeling MultiVariables with lists of Variables.')
            else:
                if not isinstance(varSubMap[relabelVar], Variable):
                    raise ValueError('May only specialize by substituting instance variables of forall operations or otherwise simply relabeling variables with variables.')
        relabMap = {k:v for k,v in varSubMap.items() if k in relabelVars}
        nonRelabSubMap = {k:v for k,v in varSubMap.items() if k not in relabelVars}
        # make and state the specialized expression with appropriate substitutions
        specializedExpr = Statement.state(expr.substituted(nonRelabSubMap, operationSubMap, relabelMap = relabMap))
        # make substitutions in the condition
        subbedConditions = {asStatement(condition.substituted(nonRelabSubMap, operationSubMap, relabelMap = relabMap)) for condition in conditions}
        Statement.state(originalExpr)
        # add the specializer link
        specializedExpr.statement.addSpecializer(originalExpr.statement, subMap, subbedConditions)
        # return the specialized expression and the 
        return specializedExpr, subbedConditions
                       
    @staticmethod
    def generalize(originalExpr, newForallVars, newConditions=None):
        '''
        State and return a generalization of a given original statement
        which derives from the original statement via a generalization inference
        rule.  This is the counterpart of specialization.  Where the original 
        has free variables taken to represent any particular 'arbitrary' values, 
        the  generalized form is a forall statement over some or all of these once
        free variables.  That is, it is statement applied to all values of any 
        of the once free variable(s) under the given condition(s).  Any condition 
        restriction is allowed because it only weakens the statement relative 
        to no condition.  The newForallVar(s) and newCondition(s) may be singular
        or plural (iterable).
        '''
        forallMaker = Operation._forallMaker()
        generalizedExpr = Statement.state(forallMaker(Lambda(newForallVars, originalExpr, newConditions)))
        Statement.state(originalExpr)
        generalizedExpr.statement.addGeneralizer(originalExpr.statement, newForallVars, newConditions)
        # In order to be a valid tautology, we have to make sure that the expression is
        # a generalization of the original.
        Statement._checkGeneralization(generalizedExpr, originalExpr)
        return generalizedExpr
    
    @staticmethod
    def _checkGeneralization(expr, instanceExpr):
        '''
        Make sure the expr is a generalize of the instanceExpr.
        '''
        FORALL = Operation._forallLiteral()
        assert isinstance(expr, Operation) and expr.operator == FORALL
        assert isinstance(expr.operand, Lambda)
        expr = expr.operand.expression
        assert expr == instanceExpr
                    
    def isAxiom(self):
        return self._isAxiom
    
    def isNamedTheorem(self):
        return self._isNamedTheorem
    
    def isProvenTheorem(self):
        '''
        A proven theorem is a proven statement without free variables (may be named or unnamed).
        '''
        return self.isProven() and len(self.getExpression().freeVars()) == 0
    
    def hasName(self):
        return not self._name is None
        
    def getContextAndName(self):
        return self._context, self._name
    
    def _tupleOfExpressions(self, expressions):
        return tuple(_expressionOrList(x) for x in expressions)
    
    def addSpecializer(self, original, subMap, conditions):
        subMap = {key:_expressionOrList(val) for key, val in subMap.iteritems()}
        self._specializers.add((original, tuple(subMap.items()), tuple(conditions)))
        original._specializations.add(self)

    def addGeneralizer(self, original, forallVars, conditions):
        if conditions is None: conditions = tuple()
        self._generalizers.add((original, tuple(forallVars), tuple([asStatement(condition) for condition in conditions])))
        original._generalizations.add(self)
        
    def addImplicator(self, hypothesis, implication):
        if (hypothesis, implication) in self._implicators:
            return # already in implicators list
        self._implicators.add((hypothesis, implication))
        implication._hypothesisOfImplication = hypothesis
        implication._conclusionOfImplication = self
        hypothesis._implicationsOfHypothesis.add(implication)

    def getProver(self, assumptions=frozenset()):
        '''
        If this statement was proven under the given assumptions and this proof is to be
        remembered (i.e., not a clear temporary proof), returns the Prover that proves 
        this statement; otherwise, returns None.
        '''
        from prover import Prover
        if self._prover != None:
            return self._prover # proof requiring no assumptions
        if len(assumptions) > 0:
            assumptions = frozenset(assumptions)
            return Prover.getProver(self, assumptions)
        
    def getOrMakeProver(self, assumptions=frozenset()):
        '''
        If this statement was proven, returns the Prover that proves this statement;
        otherwise, returns a new Prover to be used to find the proof or explore the possibilities.
        '''
        from prover import Prover
        prover = self.getProver(assumptions)
        if prover != None:
            return prover
        return Prover(self, assumptions)    
    
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.
        """
        from prover import Prover
        return Prover.isProven(self, assumptions, maxDepth, markProof)
        
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
    