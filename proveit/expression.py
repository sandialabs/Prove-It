"""
This is the expression module.
"""

import re

STRING = 1
LATEX = 2

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
            
    def formatted(self, formatType, fence=False):
        '''
        Returns a formatted version of the expression for the given formatType
        (STRING, MATHML, ...).  If fence is True, then parenthesis around 
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
        if self.isProven(assumptions)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
    
    def qed(self, filename):
        import os
        import os.path as path
        import proveit
        proofsdir, thmname = path.split(filename)
        # remove the file extension, and any optional suffix after a space
        thmname = thmname.split('.')[0].split()[0]
        theorems_abspath = path.abspath(path.join(proofsdir, '../theorems'))
        theorems_relpath =  path.relpath(theorems_abspath, start=path.join(path.split(proveit.__file__)[0], '..'))
        thm_import = __import__(theorems_relpath.replace(os.sep, '.'), fromlist=[thmname])
        thm = thm_import.__dict__[thmname]
        if not thm == self:
            raise ProofFailure('Theorem statement does not match qed expression:\n' + str(thm) + ' vs\n' + str(self))
        self.prove()
        print thmname, 'proven:'
        print self
    
    def check(self, assumptions=frozenset()):
        """
        Check that this statement is true under the given assumptions but not for a step
        of a theorem proof (that is, temporary provers aren't stored).
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        if self.isProven(assumptions, markProof=False)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
        
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.
        """
        from statement import Statement
        if self.statement == None: Statement.state(self)
        if not isinstance(self.statement, Statement):
            raise TypeError('Expression statement must be of Statement type')
        return self.statement.isProven(assumptions, maxDepth, markProof)
    
    def wasProven(self, assumptions=frozenset()):
        """
        Returns True iff this statement has already be proven under the given assumptions.
        """
        from statement import Statement
        if self.statement == None:
            return False
        else:
            if not isinstance(self.statement, Statement):
                raise TypeError('Expression statement must be of Statement type')
            return self.statement.wasProven(assumptions)
        
    def substituted(self, varMap, operationMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to varMap (Variable:Expression dictionary) and/or operations
        with variable operators substituted according to operationMap
        (Variable:Lambda dictionary) and/or relabeled according to  
        relabelMap (Variable:[Variable(s) or Etcetera-wrapped Variables(s)] dictionary).
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
        if len(relabelMap) != len(set(relabelMap.values())):
            raise ImproperRelabeling("Cannot relabel different Variables to the same Variable.")
    
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
        from statement import Statement
        return Statement.state(self)

    def relabel(self, relabelMap=None):
        return self._specialize_or_relabel(subMap=None, relabelMap=relabelMap)
    
    def specialize(self, subMap=None, relabelMap=None):
        # Can be overridden by the Forall implementation
        return self._specialize_or_relabel(subMap=subMap, relabelMap=relabelMap)

    def _specialize_or_relabel(self, subMap=None, relabelMap=None):
        from statement import Statement
        if subMap is None: subMap = dict()
        if relabelMap is None: relabelMap = dict()
        (specialization, conditions) = Statement.specialize(self, subMap, relabelMap)
        return specialization.check({self} | conditions)
        
    def generalize(self, forallVars, domain=None, conditions=tuple()):
        from statement import Statement
        from multiExpression import multiExpression
        from everythingLiteral import EVERYTHING
        if domain is None: domain = EVERYTHING # default is an unrestricted domain of EVERYTHING
        # Note that the prover will not pass this "check" in its current implementation
        # because it will not allow assumptions with variables in the newly created scope.
        # The solution for now is not to bother calling "check" here.
        return Statement.generalize(self, multiExpression(forallVars), domain, conditions)#.check({self})
    
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
    
    def _restrictionChecked(self, reservedVars):
        '''
        Check that a substituted expression (self) does not use any reserved variables
        (arguments of a Lambda function Expression).
        '''
        if not reservedVars is None and not self.freeVars().isdisjoint(reservedVars.keys()):
            raise ScopingViolation("Must not make substitution with reserved variables  (i.e., arguments of a Lambda function)")
        return self
        
class Literal(Expression):
    """
    A Literal expresses contextual meaning and they are not interchangeable.
    It is important that a Literal serving as the operator of an Operation 
    be provided with an operationMaker for creating the Operation-derived 
    object appropriately (so that formatting is done properly and class
    methods are available whenever substitutions are made for Expressions
    with these Operations).
    """
    def __init__(self, package, name, formatMap = None, operationMaker = None):
        Expression.__init__(self, formatMap)
        assert re.match('[A-Za-z0-9_]+', name), 'Literals must be alphanumeric or underscore.'
        self.package = package
        self.name = name
        self.operationMaker = operationMaker
        
    def __repr__(self):
        return str(self.package) + '.' + self.name
    
    def formatted(self, formatType, fence=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING or formatType == LATEX:
            return self.name

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

    def formatted(self, formatType, fence=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING or formatType == LATEX:
            return self.name

    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        May expand to an ExpressionList.
        '''
        from multiExpression import ExpressionList, isEtcVar
        if (varSubMap != None) and (self in varSubMap):
            return varSubMap[self]._restrictionChecked(reservedVars)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)
            for subVar in (subbed if isinstance(subbed, ExpressionList) else [subbed]):
                if not isinstance(subVar, Variable) and not isEtcVar(subVar):
                    raise ImproperRelabeling('Must relabel a Variable with Variable(s) and/or Etcetera-wrapped Variable(s)')
                if reservedVars != None and subVar in reservedVars.keys():
                    if self != reservedVars[subVar]:
                        raise ScopingViolation("Relabeling in violation of Variable scoping restrictions.")
            return subbed
        else:
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
        Create an operation with the given operator and operands.  The operator can be a 
        Literal, Variable, or Lambda function.  The operands may be single expression that
        will be then be wrapped by ExpressionList.
        '''
        from multiExpression import multiExpression, Block
        Expression.__init__(self)
        if not (isinstance(operator, Literal) or isinstance(operator, Variable) or isinstance(operator, Lambda)):
            raise TypeError('operator must be a Literal, Variable, or a Lambda function')
        self.operator = operator
        self.operands = multiExpression(operands)
        if isinstance(operator, Block):
            raise TypeError('A Block Expression must be within an ExpressionTensor or ExpressionList, not directly as an operand of an Operation')
        if isinstance(operator, Lambda):
            if len(self.operands) != len(operator.arguments):
                raise ValueError("Number of arguments and number of operands must match.")

    @staticmethod
    def make(operator, operands):
        if isinstance(operator, Literal) and operator.operationMaker is not None:
            operation = operator.operationMaker(operands)
            if not isinstance(operation, Operation):
                raise OperationMakerViolation(operator, 'Registered Operation maker must make an Operation type')
            if operation.operator != operator:
                raise OperationMakerViolation(operator, 'Registered Operation maker function must make an Operation true to its given operator: ' + str(operator))
            if operation.operands != operands:
                raise OperationMakerViolation(operator, 'Registered Operation maker function must make an Operation true to its given operand.  Operator: ' + str(operator) + '; Operands: ' + str(operands))
            return operation
        return Operation(operator, operands)

    def __repr__(self):
        return repr(self.operator) + '(' + repr(self.operands) +')'
        
    def formatted(self, formatType, fence=False):
        # override this default as desired
        if formatType == STRING or formatType == LATEX:
            return self.operator.formatted(formatType, fence=True) +  '(' + self.operands.formatted(formatType, fence=False) + ')'
        
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from multiExpression import ExpressionList, extractVar, multiExpression
        operator = self.operator
        subbedOperands = self.operands.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
        if operationSubMap is not None and isinstance(operator, Variable) and operator in operationSubMap:
            # Substitute the entire operation via a Lambda expression
            operatorSubs = operationSubMap[operator]
            subbedOperations = []
            for operatorSub in (operatorSubs if isinstance(operatorSubs, ExpressionList) else [operatorSubs]):
                if not isinstance(operatorSub, Lambda):
                    raise ImproperSubstitution("Operation substitution requires a Lambda function to define the new operation.")
                # Substitute the entire operation via a lambda expression
                # For example, f(x, y) -> x + y.
                if len(subbedOperands) != len(operatorSub.arguments):
                    raise ImproperSubstitution('Cannot substitute an Operation with the wrong number of arguments')
                operandSubMap = {argument:operand for argument, operand in zip(operatorSub.arguments, subbedOperands)}
                if not reservedVars is None:
                    # the reserved variables of the lambda expression excludes the lambda arguments
                    # (i.e., the arguments mask externally reserved variables).
                    lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if extractVar(k) not in operatorSub.argVarSet}
                else: lambdaExprReservedVars = None
                subbedOperations.append(operatorSub.expression._restrictionChecked(lambdaExprReservedVars).substituted(operandSubMap, None))
            if isinstance(operatorSubs, ExpressionList):
                return multiExpression(subbedOperations)
            else:
                return subbedOperations[0]
        else:
            # Can perform substitutions within the Operator
            subbedOperator = operator.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
            if isinstance(subbedOperator, ExpressionList):
                # substituting the single operation with multiple operations as an ExpressionList
                return ExpressionList([Operation.make(operator, subbedOperands) for operator in subbedOperator])
            else:                   
                return Operation.make(subbedOperator, subbedOperands)
        
    def usedVars(self):
        '''
        Returns the union of the operator and operands used variables.
        '''
        return self.operator.usedVars().union(self.operands.usedVars())
        
    def freeVars(self):
        '''
        Returns the union of the operator and operands free variables.
        '''
        return self.operator.freeVars().union(self.operands.freeVars())

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps arguments to
    an expression.  The arguments is an ExpressionList with each of its
    expressions being either a Variable or a Variable wrapped in
    Etcetera (see multiExpression.py).  For example,
    (x, y) -> sin(x^2 + y).
    '''
    def __init__(self, arguments, expression):
        '''
        Initialize a Lambda expression given arguments and an expression.
        Each argument in arguments must be a Variable or a Variable
        wrapped in Etcetera.  arguments may be an iterable of these
        or a single one that will be wrapped by ExpressionList.
        '''
        from multiExpression import ExpressionList, Block, isEtcVarOrVar, extractVar, singleOrMultiExpression
        self.arguments = arguments if isinstance(arguments, ExpressionList) else ExpressionList(arguments)
        for var in self.arguments:
            if not isEtcVarOrVar(var):
                raise TypeError('Each element of the Lambda arguments must be a Variable or Variable wrapped in Etcetera')
        self.argVarSet = {extractVar(arg) for arg in self.arguments}
        if len(self.argVarSet) != len(self.arguments):
            raise ValueError('Lambda argument Variables must be unique with respect to each other.')
        expression = singleOrMultiExpression(expression)
        if not isinstance(expression, Expression):
            raise TypeError('A Lambda expression must be of type Expression')
        if isinstance(expression, Block):
            raise TypeError('A Block Expression must be within an ExpressionTensor or ExpressionList, not directly as a Lambda expression')
        self.expression = expression
        
    def __repr__(self):
        return '[(' + ','.join(repr(var) for var in self.arguments) + ')->' + repr(self.expression) + ']'
    
    def formatted(self, formatType, fence=False):
        '''
        The default Lambda formatting is of the form "(x, y) -> f(x, y)".
        '''
        if formatType == STRING:
            outStr = '[' if fence else ''
            outStr += '(' + ', '.join([var.formatted(formatType) for var in self.arguments]) + ') -> '
            outStr += self.expression.formatted(formatType)
            if fence: outStr += ']'
        elif formatType == LATEX:
            outStr = r'\left[' if fence else ''
            outStr += r'\left(' + ', '.join([var.formatted(formatType) for var in self.arguments]) + r'\right) \rightarrow '
            outStr += self.expression.formatted(formatType)
            if fence: outStr += r'\right]'
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
        from multiExpression import ExpressionList, extractVar, NestedExpressionListsError
        # Can't substitute the lambda argument variables; they are in a new scope.
        innerVarSubMap = {key:value for (key, value) in varSubMap.iteritems() if extractVar(key) not in self.argVarSet}
        if operationSubMap is None: operationSubMap = dict()
        innerOperationSubMap = {key:value for (key, value) in operationSubMap.iteritems() if extractVar(key) not in self.argVarSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        try:
            newArgs = self.arguments.relabeled(relabelMap, reservedVars)
        except NestedExpressionListsError:
            raise ImproperRelabeling('May only relabel a Lambda argument with an ExpressionList if it was wrapped in Etcetera')
        for arg in self.arguments:
            # Here we enable an exception of relabeling to a reserved variable as
            # long as we are relabeling the Lambda argument and internal variable together.
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            # Also works with Etcetera: (x, ..y..) -> f(x, ..y..) relabeled to (x, y, z) -> f(x, y, z).
            newArg = arg.relabeled(relabelMap, reservedVars)
            if isinstance(newArg, ExpressionList):
                for x in newArg: innerReservations[extractVar(x)] = extractVar(arg)
            else: innerReservations[extractVar(newArg)] = extractVar(arg)
        # the lambda expression with the substitution:
        subbedExpr = self.expression.substituted(innerVarSubMap, innerOperationSubMap, relabelMap, innerReservations)
        try:
            newLambda = Lambda(newArgs, subbedExpr)
        except TypeError as e:
            raise ImproperSubstitution(e.message)
        except ValueError as e:
            raise ImproperSubstitution(e.message)            
        return newLambda
        
    def usedVars(self):
        '''
        The used variables the lambda function are the used variables of the expression
        plus the lambda argument variables.
        '''
        return self.expression.usedVars().union(set(self.argVarSet))
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the expression
        minus the lambda argument variables.  The lambda function binds those variables.
        '''
        innerFreeVs = set(self.expression.freeVars())
        return innerFreeVs - self.argVarSet

class ImproperSubstitution(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ImproperRelabeling(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ScopingViolation(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class OperationMakerViolation(Exception):
    def __init__(self, operator, message):
        self.operator = operator
        self.message = message
    def __str__(self):
        return self.message + ' for operator ' + self.operator.name
    
class ProofFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
