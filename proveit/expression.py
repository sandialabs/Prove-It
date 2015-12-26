"""
This is the expression module.
"""

import re
import os

STRING = 1
LATEX = 2

class Expression:
    unique_id_map = dict() # map unique_id's to unique_rep's
    expr_to_prove = None # the theorem currently being proven (if there is one)
    
    def __init__(self, coreInfo, subExpressions=tuple(), formatMap=None):
        # Will be the associated Statement if the Expression is
        # ever 'stated' in a particular prover.
        self.statement = None
        self.formatMap = formatMap
        # unique_rep is a unique representation based upon unique_id's of sub-Expressions
        self._coreInfo, self._subExpressions = coreInfo, subExpressions
        self._unique_rep = self._coreInfo + ' ' + ', '.join(hex(expr._unique_id) for expr in subExpressions)
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)
        while self._unique_id in Expression.unique_id_map and Expression.unique_id_map[self._unique_id] != self._unique_rep:
            self._unique_id += 1
        Expression.unique_id_map[self._unique_id] = self._unique_rep
        self.png = None # if a png is generate, it is stored for future reference
    
    def __repr__(self):
        return '$' + self.formatted(LATEX) + '$' # temporary convenience for writing report
        #return str(self) # just use the string representation
    
    def __eq__(self, other):
        if isinstance(other, Expression):
            return self._unique_id == other._unique_id
        else: return False # other must be an Expression to be equal to self
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return self._unique_id
    
    def _export_pvit(self, directory):
        '''
        Export the expression and sub-expressions into the given directory
        for the purposes of proof certification.  Returns the identifier of
        this expression, unique within the directory.  This occurs behind-the-
        scenes (and is therefore not a "public" method).
        '''
        import hashlib
        # export sub expressions and obtain their directory-unique ids
        sub_ids = [sub_expr._export_pvit(directory) for sub_expr in self._subExpressions]
        # generate a directory-unique representation for this expression
        unique_rep = self._coreInfo + ' ' + ', '.join(sub_id for sub_id in sub_ids) + '\n'
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        hash_dir = os.path.join(directory, rep_hash)
        if not os.path.exists(hash_dir):
            os.mkdir(hash_dir)
        # check for existing files in this hash value sub-directory (it may be there already)
        for expr_file in os.listdir(hash_dir):
            if expr_file[-6:] == '.pv_it':
                with open(os.path.join(hash_dir, expr_file), 'r') as f:
                    if f.read() == unique_rep:
                        # an existing file contains the exported expression
                        return rep_hash + '/' + expr_file[:-6]
        # does not exist, create a new file (checking against an unlikely collision)
        k = 0
        while os.path.exists(os.path.join(hash_dir, str(k) + '.pv_it')):
            k += 1
        with open(os.path.join(hash_dir, str(k) + '.pv_it'), 'w') as f:
            f.write(unique_rep)
        return rep_hash + '/' + str(k) # unique id
    
    def __str__(self):
        return self.formatted(STRING)
    
    def subExprGen(self):
        '''
        Generator over the sub-expressions of this expression.
        '''
        for subExpr in self._subExpressions:
            yield subExpr
    
    def formatted(self, formatType, fence=False):
        '''
        Returns a formatted version of the expression for the given formatType
        (STRING, MATHML, ...).  If fence is True, then parenthesis around 
        the sub-expression may be necessary to avoid ambiguity.
        '''
        if self.formatMap != None and formatType in self.formatMap:
            return self.formatMap[formatType]
        return ''
    
    def proven(self, assumptions=frozenset()):
        """
        Prove a step along the way to a theorem proof (or throw an error if the proof fails).
        Returns this proven statement expression.
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        if self.isProven(assumptions)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
    
    def beginProof(self):
        # clear all the provers
        from proveit.statement import Statement
        from proveit.prover import Prover

        # forget that this is a theorem expression so that we generate a non-trivial proof:
        for stmt in Statement.statements.values():
            # clear all of the statements to start fresh
            stmt.proofNumber = float('inf')
            stmt._prover = None
            if stmt == self.statement:
                stmt._isNamedTheorem = False
        Prover._tmpProvers.clear()
        for stmt in Statement.statements.values():
            # re-mark the axioms and theorems as proven (but not the special one we are trying to prove)
            if stmt._isAxiom or stmt._isNamedTheorem:
                Prover._markAsProven(stmt, Prover(stmt, []))
                
        Expression.expr_to_prove = self
        return self
    
    def qed(self):
        import proveit
        """
        proofsdir, proofname = os.path.split(filename)
        # remove the file extension for the proof name
        proofname = os.path.splitext(proofname)[0]
        # remove any optional suffix after a space to go from the proof name to the theorem name
        thmname = os.path.splitext(proofname)[0].split()[0]
        theorems_abspath = os.path.abspath(os.path.join(proofsdir, '../theorems'))
        theorems_relpath =  os.path.relpath(theorems_abspath, start=os.path.join(os.path.split(proveit.__file__)[0], '..'))
        thm_import = __import__(theorems_relpath.replace(os.sep, '.'), fromlist=[thmname])
        try:
            thm = thm_import.__getattr__(thmname)
        except AttributeError:
            raise ProofFailure('Theorem named ' + thmname + ' does not exist')
        if not thm == self:
            raise ProofFailure('Theorem statement does not match qed expression:\n' + str(thm) + ' vs\n' + str(self))
        # forget that this is a theorem expression so that we generate a non-trivial proof:
        self.state()
        self.statement._prover = None
        self.proven()
        pvit_path = os.path.join(os.path.split(filename)[0], '..', '__pv_it__')
        pvit_proofs_path = os.path.join(pvit_path, 'proofs')
        if not os.path.exists(pvit_proofs_path):
            os.mkdir(pvit_proofs_path)
        expressions_dir = os.path.join(pvit_path, 'expressions')
        if not os.path.exists(expressions_dir):
            os.mkdir(expressions_dir)
        pvit_proof_filename = os.path.join(pvit_proofs_path, proofname + '.pv_it')
        with open(pvit_proof_filename, 'w') as pvit_proof_file:
            self.statement.getProver()._export_pvit(pvit_proofs_path, pvit_proof_file, expressions_dir)
        """
        if not Expression.expr_to_prove == self:
            raise ProofFailure('Theorem statement does not match qed expression:\n' + str(Expression.expr_to_prove) + ' vs\n' + str(self))
        self.proven()
        self.statement.getProver().showProof()
        return self
    
    def checked(self, assumptions=frozenset()):
        """
        Check that this statement is true under the given assumptions but not for a step
        of a theorem proof (that is, temporary provers aren't stored).  Returns
        this checked statement expression.
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        if self.isProven(assumptions, markProof=False)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
        
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to proven this statement under the given assumptions.  If a proof derivation
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
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the expressions substituted 
        according to the exprMap dictionary (mapping Expressions to Expressions --
        for specialize, this may only map Variables to Expressions).
        If supplied, reservedVars is a dictionary that maps reserved Variable's
        to relabeling exceptions.  You cannot substitute with an expression that
        uses a restricted variable and you can only relabel the exception to the
        restricted variable.  This is used to protect an Lambda function's "scope".
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return self
    
    def relabeled(self, relabelMap, reservedVars=None):
        '''
        A watered down version of substitution in which only variable labels are
        changed.  This may also involve substituting a MultiVariable with a list
        of Variables.
        '''
        return self.substituted(exprMap=dict(), relabelMap=relabelMap, reservedVars=reservedVars)
    
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

    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        return set()    

    def safeDummyVar(self):
        return safeDummyVar(self)

    def safeDummyVars(self, n):
        dummyVars = []
        for _ in range (n):
            dummyVars.append(safeDummyVar(*([self] + dummyVars)))
        return dummyVars
    
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
        return specialization.checked({self} | conditions)
        
    def generalize(self, forallVars, domain=None, conditions=tuple()):
        from statement import Statement
        from multiExpression import multiExpression
        from everythingLiteral import EVERYTHING
        if domain is None: domain = EVERYTHING # default is an unrestricted domain of EVERYTHING
        # Note that the prover will not pass this "checked" in its current implementation
        # because it will not allow assumptions with variables in the newly created scope.
        # The solution for now is not to bother calling "checked" here.
        return Statement.generalize(self, multiExpression(forallVars), domain, conditions)#.checked({self})
    
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
        First attempt to proven the Statement of this Expression, then
        show the derivation tree of the proof.
        '''
        self.proven(assumptions).show(assumptions)
    """
    
    def proveByEval(self):
        '''
        Prove self by calling self.evaluate() if it equates the expression to TRUE.
        The evaluate method must be implemented by the derived class.
        '''
        return self.evaluate().deriveViaBooleanEquality().proven()
    
    def _restrictionChecked(self, reservedVars):
        '''
        Check that a substituted expression (self) does not use any reserved variables
        (arguments of a Lambda function Expression).
        '''
        if not reservedVars is None and not self.freeVars().isdisjoint(reservedVars.keys()):
            raise ScopingViolation("Must not make substitution with reserved variables  (i.e., arguments of a Lambda function)")
        return self

    # THIS USES MATHJAX WHICH IS LESS FLEXIBLE THAN DVIPNG (BELOW)  
    """
    def _repr_latex_(self):
        return '$' + self.formatted(LATEX) + '$'
    """
    """
    def _repr_png_(self):
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        if not hasattr(self,'png') or self.png is None:
            LaTeXTool.clear_instance()
            lt = LaTeXTool.instance()
            lt.use_breqn = False
            self._config_latex_tool(lt)
            self.png = latex_to_png(self.formatted(LATEX), backend='dvipng', wrap=True)
        return self.png
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        for sub_expr in self._subExpressions:
            sub_expr._config_latex_tool(lt)
    """
    
    def showNestedSubExpressions(self):
        from multiExpression import NamedExpressions
        visitedExpressions = set()
        nextExpressions = [self]
        enumeratedExpressions = []
        while len(nextExpressions) > 0:
            nextExpr = nextExpressions.pop(0)
            if nextExpr in visitedExpressions: continue # already showed that one
            visitedExpressions.add(nextExpr)
            enumeratedExpressions.append(nextExpr)
            nextExpressions += nextExpr._subExpressions
        exprNumMap = {expr:k for k, expr in enumerate(enumeratedExpressions)}
        print r'\begin{tabular}{rl|l|l}'
        print r' & \textbf{expression} & \textbf{core type} & \textbf{sub-expressions} \\'
        for k, expr in enumerate(enumeratedExpressions):
            print r'\hline'
            print str(k) + '. & ' + repr(expr) + ' & ' + expr._coreInfo.split()[0] + ' & '
            if isinstance(expr, NamedExpressions):
                print r'$\begin{array}{l}'
                for key in sorted(expr.keys()):
                    print r'\rm{' + key.replace('_', r'\_') + '}: ' + str(exprNumMap[expr[key]]) + r'\\'
                print r'\end{array}$ \\'
            elif isinstance(expr, Operation):
                print r'$\begin{array}{l}'
                print r'\rm{operator}: ' + str(exprNumMap[expr.operator]) + r' \\'
                print r'\rm{operands}: ' + str(exprNumMap[expr.operands]) + r' \\'
                print r'\end{array}$ \\'
            elif isinstance(expr, Lambda):
                print r'$\begin{array}{l}'
                print r'\rm{arguments}: ' + str(exprNumMap[expr.arguments]) + r' \\'
                print r'\rm{expression}: ' + str(exprNumMap[expr.expression]) + r' \\'
                print r'\end{array}$ \\'
            else:
                print ', '.join(str(exprNumMap[subExpr]) for subExpr in expr._subExpressions) + r'\\'
        print r'\hline'
        print r'\end{tabular}'
            
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
        Expression.__init__(self, 'Literal ' + str(package) + '.' + name, formatMap=formatMap)
        assert re.match('[A-Za-z0-9_]+', name), 'Literals must be alphanumeric or underscore.'
        self.package = package
        if package is None or self.package[:7] != 'proveit':
            raise Exception('Literal package must be contained within proveit.  This may result from a relative import.\nUse absolute imports with proveit Literals.')
        self.name = name
        self.operationMaker = operationMaker
            
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
        Expression.__init__(self, 'Variable ' + name, formatMap=formatMap)
        assert re.match('[A-Za-z0-9_]+', name), 'Variables must be alphanumeric or underscore.'
        self.name = name
        
    def formatted(self, formatType, fence=False):
        # override this default as desired
        fromFormatMap = Expression.formatted(self, formatType)
        if fromFormatMap != '': return fromFormatMap
        if formatType == STRING or formatType == LATEX:
            return self.name

    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        May expand to an ExpressionList.
        '''
        from multiExpression import ExpressionList, isBundledVar
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)
            for subVar in (subbed if isinstance(subbed, ExpressionList) else [subbed]):
                if not isinstance(subVar, Variable) and not isBundledVar(subVar):
                    raise ImproperRelabeling('May only relabel a Variable with Variable(s) and/or Bundled Variable(s)')
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

    def freeMultiVars(self):
        return set() # overridden in MultiVariable
    
class IndexVariable(Variable):
    def __init__(self, n):
        Variable.__init__(self, '_' + str(n) + '_', {LATEX: r'\_' + str(n) + r'\_'})

def safeDummyVar(*expressions):
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
        from multiExpression import multiExpression, MultiVariable
        if not (isinstance(operator, Literal) or isinstance(operator, Variable) or isinstance(operator, MultiVariable)):
            raise TypeError('operator must be a Literal, Variable, or MultiVariable')
        self.operator = operator
        self.operands = multiExpression(operands)
        if isinstance(operator, Lambda):
            if len(self.operands) != len(operator.arguments):
                raise ValueError("Number of arguments and number of operands must match.")
        Expression.__init__(self, 'Operation', [self.operator, self.operands])

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
        
    def formatted(self, formatType, fence=False):
        # override this default as desired
        if formatType == STRING:
            return self.operator.formatted(formatType, fence=True) +  '(' + self.operands.formatted(formatType, fence=False, subFence=False) + ')'
        elif formatType == LATEX:
            return self.operator.formatted(formatType, fence=True) +  r'\left(' + self.operands.formatted(formatType, fence=False, subFence=False) + r'\right)'
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from multiExpression import extractVar, Etcetera
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        operator = self.operator
        subbedOperands = self.operands.substituted(exprMap, relabelMap, reservedVars)
        subbedOperator = self.operator.substituted(exprMap, relabelMap, reservedVars)
        # Not allowed to substitute the operator or operation if there are Etcetera operands
        # because the number of operands should not be indeterminate when performing such a substition.
        for subbedOperand in subbedOperands:
            if isinstance(subbedOperand, Etcetera):
                if subbedOperator != operator:
                    raise Exception('Not allowed to perform an Operation substition with any remaining Etcetera operands because the number of operands should be determined when substititing the operation.')
        if isinstance(subbedOperator, Lambda):
            # Substitute the entire operation via a Lambda expression
            # For example, f(x, y) -> x + y.
            if len(subbedOperands) != len(subbedOperator.arguments):
                raise ImproperSubstitution('Cannot substitute an Operation with the wrong number of arguments')
            operandSubMap = {argument:operand for argument, operand in zip(subbedOperator.arguments, subbedOperands)}
            if not reservedVars is None:
                # the reserved variables of the lambda expression excludes the lambda arguments
                # (i.e., the arguments mask externally reserved variables).
                lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if extractVar(k) not in subbedOperator.argVarSet}
            else: lambdaExprReservedVars = None
            return subbedOperator.expression._restrictionChecked(lambdaExprReservedVars).substituted(operandSubMap, None)
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
    
    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        return self.operator.freeMultiVars().union(self.operands.freeMultiVars())

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps arguments to
    an expression.  The arguments is an ExpressionList with each of its
    expressions being either a Variable or a Bundled Variable 
    (see multiExpression.py).  For example, (x, y) -> sin(x^2 + y).
    '''
    def __init__(self, arguments, expression):
        '''
        Initialize a Lambda expression given arguments and an expression.
        Each argument in arguments must be a Variable or a Bundled Variable.
        arguments may be an iterable of these or a single one that will be 
        wrapped by ExpressionList.
        '''
        from multiExpression import ExpressionList, Bundle, isBundledVarOrVar, extractVar, singleOrMultiExpression
        self.arguments = arguments if isinstance(arguments, ExpressionList) else ExpressionList(arguments)
        for var in self.arguments:
            if not isBundledVarOrVar(var):
                raise TypeError('Each element of the Lambda arguments must be a Variable or Bundled Variable')
        self.argVarSet = {extractVar(arg) for arg in self.arguments}
        if len(self.argVarSet) != len(self.arguments):
            raise ValueError('Lambda argument Variables must be unique with respect to each other.')
        expression = singleOrMultiExpression(expression)
        if not isinstance(expression, Expression):
            raise TypeError('A Lambda expression must be of type Expression')
        if isinstance(expression, Bundle):
            raise TypeError('A Bundle must be within an ExpressionTensor or ExpressionList, not directly as a Lambda expression')
        self.expression = expression
        Expression.__init__(self, 'Lambda', [self.arguments, self.expression])
        
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
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Return this expression with its variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        The Lambda argument(s) have their own scope within the Lambda 
        expression or domainCondition and do not get substituted.  They may be
        relabeled, however.  Substitutions within the Lambda expression are 
        restricted to exclude the Lambda argument(s) themselves (these Variables 
        are reserved), consistent with any relabeling.
        '''
        from multiExpression import ExpressionList, extractVar, NestedMultiExpressionError
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        # Can't substitute the lambda argument variables; they are in a new scope.
        innerExprMap = {key:value for (key, value) in exprMap.iteritems() if extractVar(key) not in self.argVarSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        try:
            newArgs = self.arguments.relabeled(relabelMap, reservedVars)
        except NestedMultiExpressionError as e:
            raise ImproperRelabeling('May only relabel a Lambda argument with a MultiExpression if it was wrapped in the appropriate Bundle: ' + e.msg)
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
        subbedExpr = self.expression.substituted(innerExprMap, relabelMap, innerReservations)
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
    
    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        innerFreeVs = set(self.expression.freeMultiVars())
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
