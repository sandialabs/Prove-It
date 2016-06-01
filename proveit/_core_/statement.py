"""
This is the statement module.
"""

from proveit._core_.expression import Lambda, Operation, Expression, Variable, ExpressionTensor, ExpressionList
from proveit._core_.expression.composite.composite import Composite, compositeExpression, singleOrCompositeExpression
from proveit._core_.expression.bundle import isBundledVar, isBundledVarOrVar, isBundledOperation
            
def asStatement(statementOrExpression):
    '''
    Given an expression, returns the corresponding statement (made in the current prover).
    Given a statement, returns what was given.
    '''
    if isinstance(statementOrExpression, Statement):
        return statementOrExpression
    return Statement.state(statementOrExpression).statement

class Statement:
    # All Statements, mapped by Expression ids.
    statements = dict()

    ProofCount = 0 # counter to number each proof
    utilizedProofNumbers = set() #  don't remove from _assumptionSetsForWhichProven of a ProofStepInfo unless it's proofnumber is not utilized
    
    def __init__(self, expression, _package=None, _name=None, _isAxiom=False, _isNamedTheorem=False):
        '''
        Do not use the Statement constructor externally.  Instead, do so indirectly;
        via the state method of an Expression or other Expression methods that
        generate new Statements from old Statements.
        '''
        self._expression = expression
        self._package = _package
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
    def state(expression, _package=None, _name=None, _isAxiom=False, _isNamedTheorem=False):
        '''
        Make a Statement from the given Expression and return the Expression.
        '''
        from prover import Prover
        from proveit import Implies
        
        statement = Statement(expression, _package, _name, _isAxiom, _isNamedTheorem)
        statement = Statement.statements.setdefault(expression._unique_id, statement)
        if _isAxiom or _isNamedTheorem:
            assert _package is not None and _name is not None, "Theorems and Axioms must have a package and name"
        expression.statement = statement        
        
        if _isAxiom or _isNamedTheorem:
            # Mark as proven up to axioms and theorems. The proof won't be really complete until required
            # theorems are completely proven, but the proof steps will be in place in any case. 
            assert len(expression.freeVars()) == 0, "Axioms and theorems may not have free variables: " + _name + ', ' + str(expression.freeVars())
            Prover._markAsProven(statement, Prover(statement, []))
            
        # When stating an implication, link together the implication, hypothesis and conclusion
        if isinstance(expression, Implies) and len(expression.operands) == 2:
            implication = statement
            hypothesis = Statement.state(expression.operands[0]).statement
            conclusion = Statement.state(expression.operands[1]).statement
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
    def specialize(originalExpr, subMap, relabelMap):
        '''
        State and return a tuple of (specialization, conditions).  The 
        specialization derives from the given original statement and its conditions
        via a specialization inference rule.  It is the specialized form of the 'original' 
        expression by substituting one or more instance variables of outer Forall operations 
        according to the substitution map (subMap) and/or relabeling variables 
        according to the relabeling map (relabelMap).  Unless subMap is empty,
        the outer Forall is eliminated in the process and as a result there may end 
        up being free variables which can be considered to be "arbitrary" variables 
        used in logical reasoning.  Eventually they should be bound again via 
        generalization (the counterpart to specialization).
        '''
        from proveit import Forall, InSet
        
        # Check the relabelMap and convert Etcetera-wrapped relabelMap keys to Variable keys
        origRelabelItems = list(relabelMap.iteritems())
        relabelMap = dict()
        for key, sub in origRelabelItems:
            if isinstance(key, Variable):
                if not isinstance(sub, Variable):
                    raise ImproperSpecialization('May only relabel a Variable to a Variable.')
                relabelVar = key
            elif isBundledVar(key):                
                sub = compositeExpression(sub)
                if not isinstance(sub, ExpressionList):
                    raise ImproperSpecialization('May only relabel a Bundled Variable to a single (Bundled) Variable or list of (Bundled) Variables')
                for v in sub:
                    if not isBundledVarOrVar(v) or (isBundledVar(v) and v.multiExprType != key.multiExprType):
                        raise ImproperSpecialization('May only relabel a Bundled Variable to Bundled Variables of the same type')
                # change ..x..:expression_or_expressions to x:expressions
                relabelVar = key.bundledExpr.variable
            else:
                raise ImproperSpecialization("May only relabel a Variable or a Bundled Variable")   
            relabelMap[relabelVar] = sub
        # Process the substitution map, performming conversions of Operations and Etcetera-wrapped Operations/Variables
        substitutingVars = set()
        origSubMapItems = list(subMap.iteritems())
        subMap = dict()
        for subKey, sub in origSubMapItems:
            if isinstance(subKey, Variable):
                # substitute a simple Variable
                if not isinstance(sub, Expression) or isinstance(sub, Composite):
                    raise ImproperSpecialization('A normal Variable may be not be specialized to a composite Expression (only a Bundled Variable may be)')
                subVar = subKey
                subMap[subVar] = sub
            elif isBundledVar(subKey):
                # substitute an Etcetera-wrapped Variable -- sub in an ExpressionList
                subVar = subKey.bundledExpr.variable
                sub = compositeExpression(sub)
                if sub.__class__ != subKey.multiExprType:
                    if subKey.multiExprType == ExpressionList:
                        raise ImproperSpecialization('Etcetera Variables may only be specialized to a list of Expressions')
                    elif subKey.multiExprType == ExpressionTensor:
                        raise ImproperSpecialization('Block Variables may only be specialized to a tensor of Expressions')
                    else:
                        raise ImproperSpecialization('Unknown Bundle type:' + str(subKey.multiExprType))
                subMap[subVar] = sub
            elif isinstance(subKey, Operation) or isBundledOperation(subKey):
                # Substitute an Operation, f(x):expression, or a Bundled operation like
                # ..Q(x)..:expressions.
                # These get converted in the subMap to a map of the operator Variable
                # to a lambda, e.g. f:(x->expression) or Q:(x->expressions)
                operation = subKey if isinstance(subKey, Operation) else subKey.bundledExpr
                try:
                    if isinstance(subKey, Operation):
                        if not isinstance(sub, Expression) or isinstance(sub, Composite):
                            raise ImproperSpecialization('A normal operation may be not be specialized to a composite Expression (only a Bundled Operation may be)')                    
                        lambdaExpr = sub
                        subVar = operation.operator
                        subMap[subVar] = Lambda(operation.operands, lambdaExpr)
                    else: 
                        lambdaExpressions = compositeExpression(sub)
                        subVar = operation.operator.variable
                        subMap[subVar] = ExpressionList([Lambda(operation.operands, lambdaExpr) for lambdaExpr in lambdaExpressions])
                except TypeError as e:
                    raise ImproperSpecialization("Improper Operation substitution, error transforming to Lambda: " + e.message)
                except ValueError as e:
                    raise ImproperSpecialization("Improper Operation substitution, error transforming to Lambda: " + e.message)
            else:
                raise ImproperSpecialization("Substitution may only map (Bundled) Variable types or (Bundled) Operations that have Variable operators")
            substitutingVars.add(subVar)
        if len(subMap) > 0:
            # an actual Forall specialization
            assert isinstance(originalExpr, Forall), 'May only perform substitution specialization on Forall Expressions (relabeling would be okay)'
            expr = originalExpr.operands
            lambdaExpr = expr['instance_mapping']
            domain = expr['domain']
            assert isinstance(lambdaExpr, Lambda), "Forall Operation bundledExpr must be a Lambda function, or a dictionary mapping 'lambda' to a Lambda function"
            # extract the instance expression and instance variables from the lambda expression        
            instanceVars, expr, conditions  = lambdaExpr.arguments, lambdaExpr.expression['instance_expression'], list(lambdaExpr.expression['conditions'])
            iVarSet = set().union(*[iVar.freeVars() for iVar in instanceVars])
            assert substitutingVars == iVarSet, 'The set of substituting variables must be that same as the set of Forall instance variables'
            for arg in lambdaExpr.arguments:
                if isinstance(arg, Variable) and arg in substitutingVars and isinstance(substitutingVars, ExpressionList):
                    raise ImproperSpecialization("May only specialize a Forall instance variable with an ExpressionList if it is wrapped in Etcetera")
        else:
            # just a relabeling
            expr = originalExpr
            instanceVars = []
            conditions = []
            domain = None
        # make and state the specialized expression with appropriate substitutions
        specializedExpr = Statement.state(expr.substituted(subMap, relabelMap))
        # make substitutions in the condition
        subbedConditions = {asStatement(condition.substituted(subMap, relabelMap)) for condition in conditions}
        # add conditions for satisfying the domain restriction if there is one
        if domain is not None:
            # extract all of the elements
            for var in instanceVars:
                elementOrList = var.substituted(subMap, relabelMap)
                for element in (elementOrList if isinstance(elementOrList, ExpressionList) else [elementOrList]):
                    subbedConditions.add(asStatement(InSet(element, domain)))
        Statement.state(originalExpr)
        # add the specializer link
        specializedExpr.statement.addSpecializer(originalExpr.statement, instanceVars, subMap, relabelMap, subbedConditions)
        # return the specialized expression and the 
        return specializedExpr, subbedConditions
                       
    @staticmethod
    def generalize(originalExpr, newForallVars, newDomain=None, newConditions=tuple()):
        '''
        State and return a generalization of a given original statement
        which derives from the original statement via a generalization inference
        rule.  This is the counterpart of specialization.  Where the original 
        has free variables taken to represent any particular 'arbitrary' values, 
        the  generalized form is a forall statement over some or all of these once
        free variables.  That is, it is statement applied to all values of any 
        of the once free variable(s) under the given condition(s) and/or domain.  
        Any condition/domain  restriction is allowed because it only weakens the 
        statement relative  to no condition.  The newForallVar(s) and newCondition(s) 
        may be singular or plural (iterable).
        '''
        from proveit import Forall
        generalizedExpr = Statement.state(Forall(instanceVars=newForallVars, instanceExpr=originalExpr, domain=newDomain, conditions=newConditions))
        Statement.state(originalExpr)
        generalizedExpr.statement.addGeneralizer(originalExpr.statement, newForallVars, newDomain, newConditions)
        # In order to be a valid tautology, we have to make sure that the expression is
        # a generalization of the original.
        Statement._checkGeneralization(generalizedExpr, originalExpr)
        return generalizedExpr
    
    @staticmethod
    def _checkGeneralization(expr, instanceExpr):
        '''
        Make sure the expr is a generalization of the instanceExpr.
        '''
        from proveit import Forall
        assert isinstance(expr, Forall), 'The result of a generalization must be a Forall operation'
        expr = expr.operands
        lambdaExpr = expr['instance_mapping']
        assert isinstance(lambdaExpr, Lambda), 'A Forall Expression must be in the proper form'
        expr = lambdaExpr.expression['instance_expression']
        assert expr == instanceExpr, 'Generalization not consistent with the original expression: ' + str(expr) + ' vs ' + str(instanceExpr)
                    
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
        
    def getGroupAndName(self):
        return self._group, self._name
        
    def addSpecializer(self, original, substitutingVars, subMap, relabelMap, conditions):
        from proveit._core_.expression.bundle import extractVar
        subMap = {key:singleOrCompositeExpression(val) for key, val in subMap.iteritems()}
        varToIndex = {extractVar(var):i for i, var in enumerate(substitutingVars)}
        subMapItems = tuple([(var, subMap[var]) for var in sorted(subMap.keys(), key = lambda var : varToIndex[var])])
        relabelMapItems = tuple([(var, relabelMap[var]) for var in sorted(relabelMap.keys(), key = lambda var : var.name)])
        self._specializers.add((original, subMapItems, relabelMapItems, tuple(conditions)))
        original._specializations.add(self)

    def addGeneralizer(self, original, forallVars, domain, conditions):
        if conditions is None: conditions = tuple()
        self._generalizers.add((original, tuple(forallVars), domain, tuple([asStatement(condition) for condition in compositeExpression(conditions)])))
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
        if self._prover is not None:
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
    
class ImproperSpecialization(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

