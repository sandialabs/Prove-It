from proveItCore import *
from genericOperations import *

A = Variable('A')
B = Variable('B')
C = Variable('C')
multiA = MultiVariable('A') # A*
multiB = MultiVariable('B') # B*
multiC = MultiVariable('C') # C*
P = Variable('P')
Q = Variable('Q')
R = Variable('R')
multiQ = MultiVariable('Q')
multiR = MultiVariable('R')
x = Variable('x')
y = Variable('y')
xStar = MultiVariable('x')
yStar = MultiVariable('y')
Px = Operation(P, x)
Qx = Operation(Q, x)
Qy = Operation(Q, y)
Py = Operation(P, y)
PofA = Operation(P, A)
P_of_xStar = Operation(P, xStar)
P_of_yStar = Operation(P, yStar)
P_of_xStar_yStar = Operation(P, (xStar, yStar))
X = Variable('X')
multiQ_of_xStar = Operation(multiQ, xStar)
multiQ_of_yStar = Operation(multiQ, yStar)
multiR_of_yStar = Operation(multiR, yStar)
    
class BooleanContext(Context):
    def __init__(self):
        Context.__init__(self, 'BOOLEANS')
        self.eval = [] # list of registered evaluations
        # map Boolean expressions to eval #'s for all that have been registered:
        self.evalLookup = dict() 
        self.closures = [] # list of registered boolean closure proofs
        # map Boolean closure expressions to closure #'s for all that have been registered:
        self.closureLookup = dict()
    
    def evaluateBooleanBinaryOperation(self, operation, baseEvalFn):
        from equality import equality, f, a, b, c, x, y
        _x = operation.operand[0]
        _y = operation.operand[1]
        operator = operation.operator
        if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
            evaluation = baseEvalFn(_x, _y)
        elif (_x == TRUE or _x == FALSE):
            _b = _y.evaluate().rhs
            _c = baseEvalFn(_x, _b).rhs
            dummyVar = _x.safeDummyVar() # var that isn't in _x
            fOp = Operation(f, dummyVar)
            fOpSub =  Operation.make(operator, ExpressionList(_x, dummyVar))
            evaluation = equality.unaryEvaluation.specialize({fOp:fOpSub, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
        elif (_y == TRUE or _y == FALSE):
            _a = _x.evaluate().rhs
            _c = baseEvalFn(_a, _y).rhs
            dummyVar = _y.safeDummyVar() # var that isn't in _y
            fOp = Operation(f, dummyVar)
            fOpSub = Operation.make(operator, ExpressionList(dummyVar, _y))
            evaluation = equality.unaryEvaluation.specialize({fOp:fOpSub, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
        else:
            xEval = _x.evaluate()
            yEval = _y.evaluate()
            compose(xEval, yEval)
            _a, _b = xEval.rhs, yEval.rhs 
            _c = baseEvalFn(_a, _b).rhs
            fOp = Operation(f, (a, b))
            fOpSub = Operation.make(operator, ExpressionList(a, b))
            # f(_x, _y) = _c
            evaluation = equality.binaryEvaluation.specialize({fOp:fOpSub, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
        return evaluation    
    
    def evaluate(self, expr, evalFn):
        '''
        Lookup or perform (via evalFn) and store an evaluation of the given boolean expression.
        '''
        if expr in self.evalLookup:
            return self.eval[self.evalLookup[expr]]
        else:
            evaluation = evalFn()
            if evaluation != None:
                self.evalLookup[expr] = len(self.eval)
                self.eval.append(evaluation)
                if evaluation.qed().statement.getRegisteredVar() == None:
                    booleans.register('eval', len(booleans.eval)-1)            
            return evaluation
    
    def deduceInBool(self, expr):
        '''
        Attempt to deduce, then return, that the given expression is in the set of booleans.
        '''
        if hasattr(expr, 'deduceInBool'):
            return expr.deduceInBool()
        return inBool(expr)
    
    def stateAxioms(self):
        """
        Generates the boolean axioms.  Because of the interdependence of booleans, 
        equality, and sets, this is executed on demand after these have all loaded.
        """
        
        from sets import Union, Singleton
        from equality import Equals, NotEquals
    
        # BOOLEANS = {TRUE} union {FALSE}
        self.boolsDef = self.stateAxiom(Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE))))
    
        # FALSE != TRUE
        self.falseNotTrue = self.stateAxiom(NotEquals(FALSE, TRUE))
            
        # TRUE is a true statement
        self.trueAxiom = self.stateAxiom(TRUE)
        
        # Forall statements are in the BOOLEAN set.  If it isn't TRUE, then it is FALSE.
        # forall_{P, Q*} [forall_{x* | Q*(x*)} P(x*)] in BOOLEANS
        self.forallInBool = self.stateAxiom(Forall((P, multiQ), inBool(Forall(xStar, P_of_xStar, multiQ_of_xStar))))

        # If it's ever true, it can't always be not true.  (example exists = not never)
        # forall_{P, Q*} [exists_{x* | Q*(x*)} P(x*) = not[forall_{x* | Q*(x*)} (P(x*) != TRUE)]]
        self.existsDef = self.stateAxiom(Forall((P, multiQ), Equals(Exists(xStar, P_of_xStar, multiQ_of_xStar), Not(Forall(xStar, NotEquals(P_of_xStar, TRUE), multiQ_of_xStar)))))
        
        # forall_{P, Q*} notexists_{x* | Q*(x*)} P(x*) = not[exists_{x* | Q*(x*)} P(x*)]
        self.notExistsDef = self.stateAxiom(Forall((P, multiQ), Equals(NotExists(xStar, P_of_xStar, multiQ_of_xStar), Not(Exists(xStar, P_of_xStar, multiQ_of_xStar)))))
        
        # Truth table for NOT
        self.notF = self.stateAxiom(Equals(Not(FALSE), TRUE))
        self.notT = self.stateAxiom(Equals(Not(TRUE), FALSE))
        
        # Further defining property of NOT needed in addition to the truth table
        # because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.
        
        # forall_{A} [Not(A) = TRUE] => [A=FALSE]
        self.implicitNotF = self.stateAxiom(Forall(A, Implies(Equals(Not(A), TRUE), Equals(A, FALSE))))
        # forall_{A} [Not(A) = FALSE] => [A=TRUE]
        self.implicitNotT = self.stateAxiom(Forall(A, Implies(Equals(Not(A), FALSE), Equals(A, TRUE))))

        
        # Truth table for AND
        self.andTT = self.stateAxiom(Equals(And(TRUE, TRUE), TRUE))
        self.andTF = self.stateAxiom(Equals(And(TRUE, FALSE), FALSE))
        self.andFT = self.stateAxiom(Equals(And(FALSE, TRUE), FALSE))
        self.andFF = self.stateAxiom(Equals(And(FALSE, FALSE), FALSE))
                
        # Composition of multi-And, bypassing associativity for notational convenience:
        # forall_{A, B, C*} A and B and C* = A and (B and C*)
        self.andComposition = self.stateAxiom(Forall((A, B, multiC), Equals(And(A, B, multiC), And(A, And(B, multiC)))))
        
        # A further defining property of AND is needed in addition to the truth table
        # because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE:        
        # forall_{A*, B, C*} A* and B and C* => B
        self.andImpliesEach = self.stateAxiom(Forall((multiA, B, multiC), Implies(And(multiA, B, multiC), B)))                
                
        # Truth table for OR
        self.orTT = self.stateAxiom(Equals(Or(TRUE, TRUE), TRUE))
        self.orTF = self.stateAxiom(Equals(Or(TRUE, FALSE), TRUE))
        self.orFT = self.stateAxiom(Equals(Or(FALSE, TRUE), TRUE))
        self.orFF = self.stateAxiom(Equals(Or(FALSE, FALSE), FALSE))
        
        # Composition of multi-Or, bypassing associativity for notational convenience:
        # forall_{A, B, C*} A or B or C* = A or (B or C*)
        self.orComposition = self.stateAxiom(Forall((A, B, multiC), Equals(Or(A, B, multiC), Or(A, Or(B, multiC)))))
        
        # forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
        self.iffDef = self.stateAxiom(Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A)))))
        
        # forall_{A} A => (A = TRUE)
        self.eqTrueIntro = self.stateAxiom(Forall(A, Implies(A, Equals(A, TRUE))))
        # forall_{A} (A = TRUE) => A
        self.eqTrueElim = self.stateAxiom(Forall(A, Implies(Equals(A, TRUE), A)))
        
        # (TRUE => FALSE) = FALSE
        self.impliesTF = self.stateAxiom(Equals(Implies(TRUE, FALSE), FALSE))
        
        # forall_{A | inBool(A)} [Not(A) => FALSE] => A
        self.contradictoryValidation = self.stateAxiom(Forall(A, Implies(Implies(Not(A), FALSE), A), inBool(A)))
        # Note that implies has a deriveContradiction method that applies this axiom.
    
booleans = BooleanContext()

class TrueLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'TRUE', booleans, formatMap = {MATHML:'<mstyle mathvariant="normal"><mi>true</mi></mstyle>'})
    
    def evalEquality(self, other):
        if other == TRUE:
            return deriveStmtEqTrue(booleans.trueEqTrue)
        elif other == FALSE:
            return booleans.trueNotFalse.unfold().equateNegatedToFalse()
        
class FalseLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'FALSE', booleans, formatMap = {MATHML:'<mstyle mathvariant="normal"><mi>false</mi></mstyle>'})
    
    def evalEquality(self, other):
        if other == FALSE:
            return deriveStmtEqTrue(booleans.falseEqFalse)
        elif other == TRUE:
            return booleans.falseNotTrue.unfold().equateNegatedToFalse()

# boolean related literals
IMPLIES = booleans.addLiteral('IMPLIES')
IFF = booleans.addLiteral('IFF')
TRUE = booleans.addLiteral(literal = TrueLiteral())
FALSE = booleans.addLiteral(literal = FalseLiteral())
NOT = booleans.addLiteral('NOT')
AND = booleans.addLiteral('AND')
OR = booleans.addLiteral('OR')
BOOLEANS = booleans.addLiteral('BOOLEANS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x1D539;</mtext><mspace/></mstyle>'})
FORALL = booleans.addLiteral('FORALL')
EXISTS = booleans.addLiteral('EXISTS')
NOTEXISTS = booleans.addLiteral('NOTEXISTS')
PofTrue = Operation(P, [TRUE])
PofFalse = Operation(P, [FALSE])

def inBool(X):
    from sets import In
    return In(X, BOOLEANS)

class BooleanSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'BOOLEANS', booleans, {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x1D539;</mtext><mspace/></mstyle>'})

    def unfoldElemInSet(self, element):
        '''
        From inBool(Element), derive and return [(element = TRUE) or (element = FALSE)].
        '''
        #  [(element = TRUE) or (element = FALSE)] assuming inBool(element)
        return booleans.unfoldInBool.specialize({A:element}).deriveConclusion().check({inBool(element)})
    
    def deduceElemInSet(self, element):
        '''
        From [(element = TRUE) or (element = FALSE)], derive and return [element in BOOLEANS].
        '''   
        from equality import Equals
        # prerequisite = [(element = TRUE) or (element = FALSE)]
        prerequisite = Or(Equals(element, TRUE), Equals(element, FALSE))
        # [element in BOOLEANS] assuming prerequisite
        return booleans.foldInBool.specialize({A:element}).deriveConclusion().check({prerequisite})

    def evaluateForallInSet(self, forallStmt):
        '''
        Given a forall statement over the set of Booleans, evaluate to TRUE or FALSE
        if possible.
        '''
        from equality import Equals
        from sets import In
        assert(isinstance(forallStmt, Forall))
        firstCondition = forallStmt.condition.first()
        assert(isinstance(firstCondition, In))
        assert(firstCondition.itsSet == BOOLEANS)
        varInBool = firstCondition.element
        assert varInBool in set(forallStmt.instanceVar), "To evaluate a forall statement given a condition of being in booleans, the element in question must be one of the forall instance variables."
        instanceExpr = forallStmt.instanceExpression
        P_op = Operation(P, varInBool)
        trueInstance = instanceExpr.substituted({varInBool:TRUE})
        falseInstance = instanceExpr.substituted({varInBool:FALSE})
        if trueInstance == TRUE and falseInstance == FALSE:
            # special case of Forall_{A in BOOLEANS} A
            booleans.falseEqFalse # FALSE = FALSE
            booleans.trueEqTrue # TRUE = TRUE
            evaluation = booleans.forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr}).deriveConclusion()
        else:
            # must evaluate for the TRUE and FALSE case separately
            evalTrueInstance = trueInstance.evaluate()
            evalFalseInstance = falseInstance.evaluate()
            if isinstance(evalTrueInstance, Equals) and isinstance(evalFalseInstance, Equals):
                # proper evaluations for both cases (TRUE and FALSE)
                trueCaseVal = evalTrueInstance.rhs
                falseCaseVal = evalFalseInstance.rhs
                if trueCaseVal == TRUE and falseCaseVal == TRUE:
                    # both cases are TRUE, so the forall over booleans is TRUE
                    compose(evalTrueInstance.deriveViaBooleanEquality(), evalFalseInstance.deriveViaBooleanEquality())
                    evaluation = booleans.forallBoolEvalTrue.specialize({P_op:instanceExpr}).deriveConclusion()
                else:
                    # one case is FALSE, so the forall over booleans is FALSE
                    compose(evalTrueInstance, evalFalseInstance)
                    if trueCaseVal == FALSE and falseCaseVal == FALSE:
                        evaluation = booleans.forallBoolEvalFalseViaFF.specialize({P_op:instanceExpr}).deriveConclusion()
                    elif trueCaseVal == FALSE and falseCaseVal == TRUE:
                        evaluation = booleans.forallBoolEvalFalseViaFT.specialize({P_op:instanceExpr}).deriveConclusion()
                    elif trueCaseVal == TRUE and falseCaseVal == FALSE:
                        evaluation = booleans.forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr}).deriveConclusion()
        return evaluation
    
    def unfoldForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from sets import In
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        return booleans.unfoldForallOverBool.specialize({Operation(P, forallStmt.instanceVar): forallStmt.instanceExpression, A:forallStmt.instanceVar}).deriveConclusion().check({forallStmt})

    def foldAsForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), conclude and return it from [P(TRUE) and P(FALSE)].
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        '''
        from sets import In
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        # [P(TRUE) and P(FALSE)] => forall_{A in BOOLEANS} P(A)
        folding = booleans.foldForallOverBool.specialize({Operation(P, forallStmt.instanceVar):forallStmt.instanceExpression, A:forallStmt.instanceVar})
        folding.hypothesis.concludeViaComposition()
        return folding.deriveConclusion()

BOOLEANS = booleans.addLiteral(literal = BooleanSet())

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions = None):
        '''
        Create a Forall expression:
        forall_{instanceVar | condition} instanceExpression.
        This expresses that the instanceExpression is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpression, conditions)
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'forall'
        elif formatType == MATHML:
            return '<mo>&#x2200;</mo>'

    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.
        '''
        specialized = Expression.specialize(self, subMap)
        if conditionAsHypothesis and self.hasCondition():
            return Implies(self.condition, specialized).check({self})
        return specialized
    
    def equateMaps(self):
        '''
        From forall_{x | Q(x)} f(x) = g(x) derive and return 
        [x -> f(x) | Q(x)] = [x -> g(x) | Q(x)]
        '''
        from mapping import mapping, f, g
        from equality import Equals
        assert isinstance(self.instanceExpression, Equals), "Instance expression must be an equality to use mapSubstitution"
        fOp, fOpSub = Operation(f, self.instanceVar), self.instanceExpression.lhs
        gOp, gOpSub = Operation(g, self.instanceVar), self.instanceExpression.rhs
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        if self.hasCondition():
            return mapping.mapSubstitution.specialize({fOp:fOpSub, gOp:gOpSub, Q_op:Q_op_sub, x:self.instanceVar, y:self.instanceVar}).deriveConclusion().check({self})
        else:
            return mapping.mapOverAllSubstitution.specialize({fOp:fOpSub, gOp:gOpSub}).deriveConclusion().check({self})
    
    def unfold(self):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the condition of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        return self.condition.unfoldForall(self)
    
    def equateWithUnfolded(self):
        pass
        
    def concludeAsFolded(self):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the condition of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        return self.condition.foldAsForall(self)
    
    def deriveBundled(self):
        '''
        From a nested forall statement, derive the bundled forall statement.  For example,
        forall_{x | Q(x)} forall_{y | R(y)} P(x, y) becomes forall_{x, y | Q(x), R(y)} P(x, y).
        '''
        assert isinstance(self.instanceExpression, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpression
        composedInstanceVars = ExpressionList([self.instanceVar, innerForall.instanceVar])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        multiR_op, multiR_op_sub = Operation(multiR, innerForall.instanceVar), innerForall.condition
        return booleans.forallBundling.specialize({xStar:self.instanceVar, yStar:innerForall.instanceVar, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}).deriveConclusion().check({self})

    def _specializeUnravellingTheorem(self, theorem, *instanceVarLists):
        print instanceVarLists
        assert len(self.instanceVar) > 1, "Can only unravel a forall statement with multiple instance variables"
        if len(instanceVarLists) == 1:
            raise ValueError("instanceVarLists should be a list of 2 or more Variable lists")
        if len(instanceVarLists) > 2:
            return self.deriveUnravelled(ExpressionList(instanceVarLists[:-1]), instanceVarLists[-1]).deriveUnravelled(*instanceVarLists[:-1]).check({self})
        outerVars, innerVars = instanceVarLists
        outerVarSet, innerVarSet = set(outerVars), set(innerVars)
        assert innerVarSet | outerVarSet == set(self.instanceVar), "outerVars and innterVars must combine to the full set of instance variables"
        assert innerVarSet.isdisjoint(outerVarSet), "outerVars and innterVars must be disjoint sets"
        innerConditions = []
        outerConditions = []
        for condition in self.condition:
            if condition.freeVars().isdisjoint(innerVars):
                outerConditions.append(condition)
            else: innerConditions.append(condition)
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, outerVars), outerConditions
        multiR_op, multiR_op_sub = Operation(multiR, innerVars), innerConditions
        print P_op_sub
        print multiQ_op_sub
        print multiR_op_sub
        return theorem.specialize({xStar:outerVars, yStar:innerVars, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}) 
           
    def deriveUnravelled(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        return self._specializeUnravellingTheorem(booleans.forallUnravelling, *instanceVarLists).deriveConclusion().check({self})

    def deriveUnravelledEquiv(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y | Q(x), R(y)} P(x, y) = forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        return self._specializeUnravellingTheorem(booleans.forallBundledEquiv, *instanceVarLists).check()
        
    def evaluate(self):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        assert self.hasCondition(), "Cannot evaluate a forall statement with no conditions"
        if len(self.instanceVar) == 1:
            # start with the first condition which may then nest over subsequent conditions
            return booleans.evaluate(self, lambda : self.condition.evaluateForall(self))
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnravelledEquiv(*[condition.freeVars() for condition in self.condition]).check()
            unravelledEval = unravelledEquiv.rhs.evaluate()
            return unravelledEquiv.applyTransitivity(unravelledEval).check()            

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        return booleans.forallInBool.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).check()

Operation.registerOperation(FORALL, lambda operand : Forall(operand.argument, operand.expression, operand.domainCondition))

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'exist'
        elif formatType == MATHML:
            return '<mo>&#x2203;</mo>'

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{y | Q(x)} P(y)] from P(x) and Q(x), where x is the given exampleInstance.
        '''
        # P(x) where x is the given exampleInstance
        exampleExpr = self.instanceExpression.substituted({self.instanceVar:exampleInstance})
        # Q(x) where x is the given exampleInstance
        exampleCondition = self.condition.substituted({self.instanceVar:exampleInstance})
        # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
        return booleans.existenceByExample.specialize({Operation(P, self.instanceVar): self.instanceExpression, Operation(multiQ, self.instanceVar): self.condition, yStar:self.instanceVar}).specialize({xStar:exampleInstance}).deriveConclusion().check({exampleExpr, exampleCondition})

    def deriveNegatedForall(self):
        '''
        From [exists_{x* | Q*(x*)} Not(P(x*))], derive and return Not(forall_{x* | Q*(x*)} P(x*)).
        From [exists_{x* | Q*(x*)} P(x*)], derive and return Not(forall_{x* | Q*(x*)} (P(x*) != TRUE)).
        '''
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            return booleans.existsNotImpliesNotForall.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveConclusion().check({self})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            return booleans.existsDef.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveRightViaEquivalence().check({self})
    
    def deduceInBool(self):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        return booleans.existsInBool.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).check()

Operation.registerOperation(EXISTS, lambda operand : Exists(operand.argument, operand.expression, operand.domainCondition))

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'notexist'
        elif formatType == MATHML:
            return '<mo>&#x2204;</mo>'
        
    def unfold(self):
        '''
        Deduce and return Not(Exists_{x* | Q*(x*)} P(x*)) from NotExists_{x* | Q*(x*)} P(x*)
        '''
        Q_op, Q_op_sub = Operation(multiQ, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        return booleans.notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xStar:self.instanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self):
        '''
        Prove and return some NotExists_{x* | Q*(x*)} P(x*) assuming Not(Exists_{x* | Q*(x*)} P(x*)).
        '''
        Q_op, Q_op_sub = Operation(multiQ, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        folding = booleans.notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xStar:self.instanceVar})
        return folding.deriveConclusion().check({self.unfold()})
    
    def concludeViaForall(self):
        '''
        Prove and return either some NotExists_{x* | Q*(x*)} Not(P(x*)) or NotExists_{x* | Q*(x*)} P(x*)
        assumint forall_{x* | Q*(x*)} P(x*) or assuming forall_{x* | Q*(x*)} (P(x) != TRUE) respectively.
        '''
        from equality import NotEquals
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        operand = self.operand
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            assumption = Forall(operand.argument, operand.expression.operand, operand.domainCondition)
            return booleans.forallImpliesNotExistsNot.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveConclusion().check({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            assumption = Forall(operand.argument, NotEquals(operand.expression, TRUE), operand.domainCondition)
            return booleans.existsDefNegation.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveLeftViaEquivalence().check({assumption})

Operation.registerOperation(NOTEXISTS, lambda operand : NotExists(operand.argument, operand.expression, operand.domainCondition))
    
class Implies(BinaryOperation):
    def __init__(self, hypothesis, conclusion):
        BinaryOperation.__init__(self, IMPLIES, hypothesis, conclusion)
        self.hypothesis = hypothesis
        self.conclusion = conclusion

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '=>'
        elif formatType == MATHML:
            return '<mo>&#x21D2;</mo>'

    def deriveConclusion(self):
        '''
        From (A=>B) derive and return B assuming A.
        '''
        return self.conclusion.check({self, self.hypothesis})
                
    def applySyllogism(self, otherImpl):
        '''
        From A=>B (self) and a given B=>C (otherImpl), derive and return A=>C.
        '''
        assert isinstance(otherImpl, Implies), "expected an Implies object"
        if self.conclusion == otherImpl.hypothesis:
            return Implies(self.hypothesis, otherImpl.conclusion).check({self, otherImpl})
        elif self.hypothesis == otherImpl.conclusion:
            return Implies(otherImpl.hypothesis, self.conclusion).check({self, otherImpl})
    
    def deriveViaContradiction(self):
        '''
        From [Not(A)=>FALSE], derive and return A assuming inBool(A).
        Or from (A=>FALSE), derive and return Not(A) assuming inBool(A).
        '''
        assert self.conclusion == FALSE
        if isinstance(self.hypothesis, Not):
            stmt = self.hypothesis.operand
            return booleans.contradictoryValidation.specialize({A:stmt}).deriveConclusion().check({self, inBool(stmt)})
        else:
            return booleans.hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion().check({self, inBool(self.hypothesis)})
    
    def generalize(self, newForallVars, newConditions=tuple()):
        '''
        This makes a generalization of this expression, prepending Forall 
        operations according to newForallVars and newConditions that will bind
        'arbitrary' free variables.  This overrides the Expression version
        to absorb hypothesis into conditions if they match.  For example, 
        [A(x) => [B(x, y) => P(x, y)]] generalized forall_{x, y | A(x), B(x, y)}
        becomes forall_{x | A(x)} forall_{y | B(x, y)} P(x, y),
        '''
        hypothesizedConditions = set()
        newConditionsSet = set(newConditions)
        expr = self
        while isinstance(expr, Implies) and expr.hypothesis in newConditionsSet:
            hypothesizedConditions.add(expr.hypothesis)
            expr = expr.conclusion
        if len(hypothesizedConditions) == 0:
            # Just use the Expression version
            return Expression.generalize(self, newForallVars, newConditions)
        return Expression.generalize(expr, newForallVars, newConditions)
        #return Forall(newForallVars, expr, newConditions)

    def transposition(self):
        '''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will derive from self and return as follows:
        For [Not(A) => Not(B)], derive [Not(A) => Not(B)] => [B => A] assuming inBool(A).
        For [Not(A) => B], derive [Not(A) => B] => [Not(B) => A] assuming inBool(A), inBool(B).
        For [A => Not(B)], derive [A => Not(B)] => [B => Not(A)] assuming inBool(A).
        For [A => B], derive [A => B] => [Not(B) => Not(A)] assuming inBool(A), inBool(B)
        '''
        if isinstance(self.hypothesis, Not) and isinstance(self.conclusion, Not):
            return booleans.transpositionFromNegated.specialize({B:self.hypothesis.operand, A:self.conclusion.operand}).check({inBool(self.hypothesis.operand)})
        elif isinstance(self.hypothesis, Not):
            return booleans.transpositionFromNegatedHypothesis.specialize({B:self.hypothesis.operand, A:self.conclusion}).check({inBool(self.hypothesis.operand), inBool(self.conclusion)})
        elif isinstance(self.conclusion, Not):
            return booleans.transpositionFromNegatedConclusion.specialize({B:self.hypothesis, A:self.conclusion.operand}).check({inBool(self.hypothesis)})
        else:
            return booleans.transpositionToNegated.specialize({B:self.hypothesis, A:self.conclusion}).check({inBool(self.hypothesis), inBool(self.conclusion)})
        
    def transpose(self):
        '''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will derive from self and return as follows.
        From Not(A) => Not(B), derive and return B => A assuming inBool(A).
        From Not(A) => B, derive Not(B) => A assuming inBool(A), inBool(B).
        From A => Not(B), derive B => Not(A) assuming inBool(A).
        From A => B, derive Not(B) => Not(A) assuming inBool(A), inBool(B).
        '''
        return self.transposition().deriveConclusion()
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.impliesTT
            elif A == TRUE and B == FALSE: return booleans.impliesTF
            elif A == FALSE and B == TRUE: return booleans.impliesFT
            elif A == FALSE and B == FALSE: return booleans.impliesFF
        return booleans.evaluate(self, lambda : booleans.evaluateBooleanBinaryOperation(self, baseEvalFn))
    
    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        hypothesisInBool = booleans.deduceInBool(self.hypothesis)
        conclusionInBool = booleans.deduceInBool(self.conclusion)
        return booleans.implicationClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({hypothesisInBool, conclusionInBool})

Operation.registerOperation(IMPLIES, lambda operands : Implies(*operands))

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, A)
        self.operand = A

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'not'
        elif formatType == MATHML:
            return '<mo>&#x00AC;</mo>'

    def formatted(self, formatType, fenced=False):
        if formatType == MATHML:
            outStr = ''
            if fenced: outStr += "<mfenced separators=''>"
            outStr += '<mrow>' + self.formattedOperator(formatType) + self.operand.formatted(formatType, fenced=True) + '</mrow>'
            if fenced: outStr += '</mfenced>'
            return outStr
        else:
            return Operation.formatted(self, formatType, fenced)        
        
    def evaluate(self):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from equality import Equals
        if self.operand == TRUE: return booleans.notT
        elif self.operand == FALSE: return booleans.notF
        def doEval():
            operandEval = self.operand.evaluate()
            if operandEval.rhs == TRUE: 
                val = booleans.notT.rhs
            elif operandEval.rhs == FALSE: 
                val = booleans.notF.rhs
            return operandEval.lhsSubstitute(A, Equals(Not(A), val))
        return booleans.evaluate(self, doEval)

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        operandInBool = booleans.deduceInBool(self.operand)
        return booleans.negationClosure.specialize({A:self.operand}).check({operandInBool})
   
    def equateNegatedToFalse(self):
        '''
        From Not(A), derive and return [A = FALSE].
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalse.specialize({A:self.operand}).deriveConclusion().check({self})

    def equateFalseToNegated(self):
        '''
        From Not(A), derive and return [FALSE = A].
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalseRev.specialize({A:self.operand}).deriveConclusion().check({self})
    
    def deriveViaDoubleNegation(self):
        '''
        From Not(Not(A)), return A assuming inBool(A).
        Also see version in NotEquals for A != FALSE.
        '''
        if isinstance(self.operand, Not):
            return booleans.fromDoubleNegation.specialize({A:self.operand.operand}).deriveConclusion().check({self, inBool(A)})

    def concludeViaDoubleNegation(self):
        '''
        Prove and return self of the form Not(Not(A)) assuming A.
        Also see version in NotEquals for A != FALSE.
        '''
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return booleans.doubleNegation.specialize({A:stmt}).deriveConclusion().check({stmt})
            
    def deriveContradiction(self):
        '''
        From Not(A), derive and return A=>FALSE.
        '''
        return booleans.contradictionFromNegation.specialize({A:self.operand}).check({self})
    
    def deriveNotEquals(self):
        '''
        From Not(A=B), derive and return A != B.
        '''
        from equality import equality, Equals
        if isinstance(self.operand, Equals):
            return equality.foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}).deriveConclusion().check({self})

    def deriveNotExists(self):
        '''
        From Not(exists_{x* | Q*(x*)} P(x*)), derive and return NotExists_{x* | Q*(x*)} P(x*).
        '''
        operand = self.operand
        if isinstance(operand, Exists):
            exOperand = operand.operand # Exist's operand
            notExistsExpr = NotExists(exOperand.argument, exOperand.expression, exOperand.domainCondition)
            return notExistsExpr.concludeAsFolded().check({self})
        
    def deduceDoubleNegationEquiv(self):
        '''
        For some Not(Not(A)), derive and return A = Not(Not(A)) assuming A in BOOLEANS.
        '''
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return booleans.doubleNegationEquiv.specialize({A:Asub}).check({inBool(Asub)})

Operation.registerOperation(NOT, lambda operand : Not(operand))
        
class And(AssociativeOperation):
    def __init__(self, *operands):
        '''
        And together any number of operands: A and B and C
        '''
        AssociativeOperation.__init__(self, AND, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'and'
        elif formatType == MATHML:
            return '<mo>&#x2227;</mo>'
        
    def deriveInPart(self, indexOrExpr):
        '''
        From (A and ... and X and ... and Z) derive X.  indexOrExpr specifies 
        X either by index or the Expression.
        '''
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operand).index(indexOrExpr)
        return booleans.andImpliesEach.specialize({multiA:self.operands[:idx], B:self.operands[idx], multiC:self.operands[idx+1:]}).deriveConclusion().check({self})
        
    def deriveLeft(self):
        '''
        From (A and B), derive and return A.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(0)

    def deriveRight(self):
        '''
        From (A and B), derive and return B.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(1)
        
    def decompose(self):
        '''
        From (A and B), derive and return A, B as a tuple.
        '''        
        return (self.deriveLeft(), self.deriveRight())

    def concludeViaComposition(self):
        '''
        Prove and return some (A and B) assuming A, B.  See also the compose method to
        do this constructively.
        '''
        compose(*self.operands)
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        if len(self.operands) >= 3:
            # A and B and C* = A and (B and C*)
            compositionEquiv = booleans.andComposition.specialize({A:self.operands[0], B:self.operands[1], multiC:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.andTT
            elif A == TRUE and B == FALSE: return booleans.andTF
            elif A == FALSE and B == TRUE: return booleans.andFT
            elif A == FALSE and B == FALSE: return booleans.andFF
        return booleans.evaluate(self, lambda : booleans.evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        leftInBool = booleans.deduceInBool(self.leftOperand)
        rightInBool = booleans.deduceInBool(self.rightOperand)
        return booleans.conjunctionClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})

Operation.registerOperation(AND, lambda operands : And(*operands))

class Or(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Or together any number of operands: A or B or C
        '''
        AssociativeOperation.__init__(self, OR, *operands)
    
    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'or'
        elif formatType == MATHML:
            return '<mo>&#x2228;</mo>'

    def deriveRightIfNotLeft(self):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return booleans.orImpliesRightIfNotLeft.specialize({A:leftOperand, B:rightOperand}).deriveConclusion().check({self, Not(leftOperand), inBool(rightOperand)})

    def deriveLeftIfNotRight(self):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return booleans.orImpliesLeftIfNotRight.specialize({A:leftOperand, B:rightOperand}).deriveConclusion().check({self, Not(rightOperand), inBool(leftOperand)})
        
    def deriveCommonConclusion(self, conclusion):
        '''
        From (A or B) derive and return the provided conclusion C assuming A=>C, B=>C, A,B,C in BOOLEANS.
        '''
        # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        leftImplConclusion = Implies(leftOperand, conclusion)
        rightImplConclusion = Implies(rightOperand, conclusion)
        # (A=>C and B=>C) assuming A=>C, B=>C
        compose(leftImplConclusion, rightImplConclusion)
        return booleans.hypotheticalDisjunction.specialize({A:leftOperand, B:rightOperand, C:conclusion}).deriveConclusion().deriveConclusion().check({self, leftImplConclusion, rightImplConclusion, inBool(A), inBool(B), inBool(C)})
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        if len(self.operands) >= 3:
            # A or B or C* = A or (B or C*)
            compositionEquiv = booleans.orComposition.specialize({A:self.operands[0], B:self.operands[1], multiC:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.orTT
            elif A == TRUE and B == FALSE: return booleans.orTF
            elif A == FALSE and B == TRUE: return booleans.orFT
            elif A == FALSE and B == FALSE: return booleans.orFF
        return booleans.evaluate(self, lambda : booleans.evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'or' expression is in the set of BOOLEANS.
        '''
        leftInBool = booleans.deduceInBool(self.leftOperand)
        rightInBool = booleans.deduceInBool(self.rightOperand)
        return booleans.disjunctionClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})

Operation.registerOperation(OR, lambda operands : Or(*operands))

# if and only if: A => B and B => A
class Iff(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, IFF, A, B)
        self.A = A
        self.B = B
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '<=>'
        elif formatType == MATHML:
            return '<mo>&#x21D4;</mo>'

    def deriveLeftImplication(self):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        return booleans.iffImpliesLeft.specialize({A: self.A, B: self.B}).deriveConclusion().check({self})
        
    def deriveLeft(self):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        return self.deriveLeftImplication().deriveConclusion().check({self, self.B})

    def deriveRightImplication(self):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        return booleans.iffImpliesRight.specialize({A: self.A, B: self.B}).deriveConclusion().check({self})

    def deriveRight(self):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        return self.deriveRightImplication().deriveConclusion().check({self, self.A})
    
    def deriveReversed(self):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        return booleans.iffSymmetry.specialize({A:self.A, B:self.B}).deriveConclusion().check({self})
    
    def applyTransitivity(self, otherIff):
        '''
        From A <=> B (self) and the given B <=> C (otherIff) derive and return 
        (A <=> C) assuming self and otherIff.
        Also works more generally as long as there is a common side to the equations.
        '''
        assert isinstance(otherIff, Iff)
        if self.B == otherIff.A:
            # from A <=> B, B <=> C, derive A <=> C
            compose(self, otherIff).check({self, otherIff}) # A <=> B and B <=> C
            return booleans.iffTransitivity.specialize({A:self.A, B:self.B, C:otherIff.B}).deriveConclusion().check({self, otherIff})
        elif self.A == otherIff.A:
            # from y = x and y = z, derive x = z
            return self.deriveReversed().applyTransitivity(otherIff)
        elif self.A == otherIff.B:
            # from y = x and z = y, derive x = z
            return self.deriveReversed().applyTransitivity(otherIff.deriveReversed())
        elif self.B == otherIff.B:
            # from x = y and z = y, derive x = z
            return self.applyTransitivity(otherIff.deriveReversed())
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
        
    def definition(self):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        return booleans.iffDef.specialize({A:self.A, B:self.B}).check()
    
    def concludeViaComposition(self):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        AimplB = Implies(self.A, self.B) 
        BimplA = Implies(self.B, self.A) 
        compose(AimplB, BimplA)
        return self.definition().deriveLeftViaEquivalence().check({AimplB, BimplA})
    
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.iffTT
            elif A == TRUE and B == FALSE: return booleans.iffTF
            elif A == FALSE and B == TRUE: return booleans.iffFT
            elif A == FALSE and B == FALSE: return booleans.iffFF
        return booleans.evaluate(self, lambda : booleans.evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        leftInBool = booleans.deduceInBool(self.A)
        rightInBool = booleans.deduceInBool(self.B)
        return booleans.iffClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})
    
    def deriveEquality(self):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        return booleans.iffOverBoolImplEq.specialize({A:self.A, B:self.B}).deriveConclusion().check({self, inBool(self.A), inBool(self.B)})

Operation.registerOperation(IFF, lambda operands : Iff(*operands))

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE assuming statement.
    '''
    from equality import Equals
    return Equals(statement, TRUE).concludeBooleanEquality()

def compose(*expressions):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    print len(expressions)
    if len(expressions) == 2:
        exprA, exprB = expressions
        return booleans.conjunctionIntro.specialize({A:exprA, B:exprB}).check({exprA, exprB})
    else:
        assert len(expressions) > 2, "Compose 2 or more expressions, but not less than 2."
        rightComposition = compose(*expressions[1:])
        # A and (B and C*) = TRUE, given A, B, C*
        nestedAndEqT = deriveStmtEqTrue(compose(expressions[0], rightComposition)).check(expressions)
        # A and B and C* = A and (B and C*)
        compositionEquality = booleans.andComposition.specialize({A:expressions[0], B:rightComposition.operands[0], multiC:rightComposition.operands[1:]}).check(expressions)
        print nestedAndEqT
        print compositionEquality
        # [A and B and C*] given A, B, C*
        return compositionEquality.applyTransitivity(nestedAndEqT).deriveViaBooleanEquality().check(expressions)


# DERIVATIONS

# Not(FALSE)
booleans.deriveOnDemand('notFalse', lambda : booleans.notF.deriveViaBooleanEquality().qed())
    
# TRUE and TRUE
booleans.deriveOnDemand('trueAndTrue', lambda : booleans.andTT.deriveViaBooleanEquality().qed())
    
# TRUE or TRUE
booleans.deriveOnDemand('trueOrTrue', lambda : booleans.orTT.deriveViaBooleanEquality().qed())
    
# TRUE or FALSE
booleans.deriveOnDemand('trueOrFalse', lambda : booleans.orTF.deriveViaBooleanEquality().qed())
    
# FALSE or TRUE
booleans.deriveOnDemand('falseOrTrue', lambda : booleans.orFT.deriveViaBooleanEquality().qed())

# TRUE = TRUE
def trueEqTrueDerivation():
    from equality import Equals
    return Equals(TRUE, TRUE).concludeViaReflexivity().qed()
booleans.deriveOnDemand('trueEqTrue', trueEqTrueDerivation)

# FALSE = FALSE
def falseEqFalseDerivation():
    from equality import Equals
    return Equals(FALSE, FALSE).concludeViaReflexivity().qed()
booleans.deriveOnDemand('falseEqFalse', falseEqFalseDerivation)

# forall_{A} A => (TRUE = A)
def eqTrueRevIntroDerivation():
    return Implies(A, deriveStmtEqTrue(A).concludeBooleanEquality().deriveReversed()).generalize(A).qed()
booleans.deriveOnDemand('eqTrueRevIntro', eqTrueRevIntroDerivation)

# forall_{A} (TRUE = A) => A
def eqTrueRevElimDerivation():
    from equality import Equals
    hypothesis = Equals(TRUE, A)
    return Implies(hypothesis, hypothesis.deriveReversed().deriveViaBooleanEquality()).generalize(A).qed()
booleans.deriveOnDemand('eqTrueRevElim', eqTrueRevElimDerivation)

# forall_{A} Not(A) => [A=FALSE]
def notImpliesEqFalseDerivation():
    from equality import Equals
    # [Not(A) = TRUE] => [A = FALSE]
    booleans.implicitNotF.specialize().prove()
    # [Not(A) = TRUE] assuming Not(A)
    deriveStmtEqTrue(Not(A)).prove({Not(A)})
    # forall_{A} Not(A) => [A=FALSE]
    return Implies(Not(A), Equals(A, FALSE)).generalize(A).qed()
booleans.deriveOnDemand('notImpliesEqFalse', notImpliesEqFalseDerivation)

# forall_{A} Not(A) => (FALSE = A)
def notImpliesEqFalseRevDerivation():
    return Implies(Not(A), Not(A).equateNegatedToFalse().deriveReversed()).generalize(A).qed()
booleans.deriveOnDemand('notImpliesEqFalseRev', notImpliesEqFalseRevDerivation)

# forall_{A} Not(Not(A)) => A
def fromDoubleNegationDerivation():
    # [Not(Not(A)) = TRUE] => [Not(A) = FALSE]
    booleans.implicitNotF.specialize({A:Not(A)}).prove()
    # [Not(A) = FALSE] => [A = TRUE]
    booleans.implicitNotT.specialize().prove()
    # [Not(Not(A)) = TRUE] assuming Not(Not(A))
    deriveStmtEqTrue(Not(Not(A))).prove({Not(Not(A))})
    # forall_{A} Not(Not(A)) => A
    return Implies(Not(Not(A)), A).generalize(A).qed()
booleans.deriveOnDemand('fromDoubleNegation', fromDoubleNegationDerivation)

# forall_{A} A => TRUE, by a trivial hypothetical reasoning
booleans.deriveOnDemand('trueConclusion', lambda : Implies(A, TRUE).generalize(A).qed())

# forall_{A} A => A, by a trivial hypothetical reasoning
booleans.deriveOnDemand('selfImplication', lambda : Implies(A, A).generalize(A).qed())

# (TRUE => TRUE) = TRUE
booleans.deriveOnDemand('impliesTT', lambda : deriveStmtEqTrue(booleans.trueConclusion.specialize({A:TRUE})).qed())

# (FALSE => TRUE) = TRUE
booleans.deriveOnDemand('impliesFT', lambda : deriveStmtEqTrue(booleans.trueConclusion.specialize({A:FALSE})).qed())

# (FALSE => FALSE) = TRUE
booleans.deriveOnDemand('impliesFF', lambda : deriveStmtEqTrue(booleans.selfImplication.specialize({A:FALSE})).qed())

# forall_{A, B} (A <=> B) => (A => B)
booleans.deriveOnDemand('iffImpliesRight', lambda : Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveLeft()).generalize((A, B)).qed())

# forall_{A, B} (A <=> B) => (B => A)
booleans.deriveOnDemand('iffImpliesLeft', lambda : Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveRight()).generalize((A, B)).qed())

# forall_{A, B} (A <=> B) => (B <=> A)
def iffSymmetryDerivation():
    hypothesis = Iff(A, B) # hypothesis = (A <=> B)
    # A => B given hypothesis
    hypothesis.deriveRightImplication().prove({hypothesis})
    # B => A given hypothesis
    hypothesis.deriveLeftImplication().prove({hypothesis})
    # forall_{A, B} (A <=> B) => (B <=> A)
    return Implies(hypothesis, Iff(B, A).concludeViaComposition()).generalize((A, B)).qed()
booleans.deriveOnDemand('iffSymmetry', iffSymmetryDerivation)

# forall_{A, B, C} (A <=> B and B <=> C) => (A <=> C)
def iffTransitivityDerivation():    
    # hypothesis = (A <=> B) and (B <=> C)
    hypothesis = And(Iff(A, B), Iff(B, C))
    AiffB, BiffC = hypothesis.decompose() 
    # B assuming A <=> B and A
    AiffB.deriveRight().prove({AiffB, A}) 
    # A => C assuming A <=> B, B <=> C
    Implies(A, BiffC.deriveRight()).prove({hypothesis})      
    # C assuming B <=> C and C
    BiffC.deriveLeft().prove({BiffC, C})
    # C => A assuming A <=> B, B <=> C
    Implies(C, AiffB.deriveLeft()).prove({hypothesis})   
    # A <=> C assuming hypothesis
    AiffC = Iff(A, C).concludeViaComposition().prove({hypothesis})
    # forall_{A, B, C} (A <=> B and B <=> C) => (A <=> C)
    return Implies(hypothesis, AiffC).generalize((A, B, C)).qed()
booleans.deriveOnDemand('iffTransitivity', iffTransitivityDerivation)

# Not(TRUE) => FALSE
booleans.deriveOnDemand('notTimpliesF', lambda : booleans.notT.rightImplViaEquivalence().qed())

# (TRUE <=> TRUE) = TRUE
def iffTTderivation():
    # (TRUE <=> TRUE) = (TRUE => TRUE) and (TRUE => TRUE)
    iffSpecTT = Iff(TRUE, TRUE).definition()
    # [(TRUE => TRUE) and (TRUE => TRUE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = booleans.impliesTT.substitution(X, And(X, X)).applyTransitivity(booleans.andTT).prove()
    # (TRUE <=> TRUE) = TRUE
    return iffSpecTT.applyTransitivity(rhsEqT).qed()
booleans.deriveOnDemand('iffTT', iffTTderivation)

# (FALSE <=> FALSE) = TRUE
def iffFFderivation():
    # (FALSE <=> FALSE) = (FALSE => FALSE) and (FALSE => FALSE)
    iffSpecFF = Iff(FALSE, FALSE).definition()
    # [(FALSE => FALSE) and (FALSE => FALSE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = booleans.impliesFF.substitution(X, And(X, X)).applyTransitivity(booleans.andTT).prove()
    # (FALSE <=> FALSE) = TRUE
    return iffSpecFF.applyTransitivity(rhsEqT).qed()
booleans.deriveOnDemand('iffFF', iffFFderivation)

# (TRUE <=> FALSE) = FALSE
def iffTFderivation():
    # (TRUE <=> FALSE) = (TRUE => FALSE) and (FALSE => TRUE)
    iffSpecTF = Iff(TRUE, FALSE).definition()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and (FALSE => TRUE)]
    rhsEqFandFimplT = booleans.impliesTF.substitution(X, And(X, booleans.impliesFT.lhs)).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and TRUE]
    rhsEqFandT = rhsEqFandFimplT.applyTransitivity(booleans.impliesFT.substitution(X, And(FALSE, X))).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = FALSE
    rhsEqF = rhsEqFandT.applyTransitivity(booleans.andFT).prove()
    # (TRUE <=> FALSE) = FALSE
    return iffSpecTF.applyTransitivity(rhsEqF).qed()
booleans.deriveOnDemand('iffTF', iffTFderivation)

# (FALSE <=> TRUE) = FALSE
def iffFTderivation():
    # (FALSE <=> TRUE) = (FALSE => TRUE) and (TRUE => FALSE)
    iffSpecFT = Iff(FALSE, TRUE).definition()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = [(FALSE => TRUE) and FALSE]
    rhsEqFimplTandF = booleans.impliesTF.substitution(X, And(booleans.impliesFT.lhs, X)).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = [TRUE and FALSE]
    rhsEqTandF = rhsEqFimplTandF.applyTransitivity(booleans.impliesFT.substitution(X, And(X, FALSE))).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = FALSE
    rhsEqF = rhsEqTandF.applyTransitivity(booleans.andTF).prove()
    # (TRUE <=> FALSE) = FALSE
    return iffSpecFT.applyTransitivity(rhsEqF).qed()
booleans.deriveOnDemand('iffFT', iffFTderivation)

# forall_{A | A, B | B} (A and B)
def conjunctionIntroDerivation():
    # A=TRUE assuming A
    AeqT = deriveStmtEqTrue(A).prove({A})
    # B=TRUE assuming B
    BeqT = deriveStmtEqTrue(B).prove({B})
    # TRUE AND TRUE
    booleans.trueAndTrue
    # (TRUE and B) assuming B via (TRUE and TRUE)
    BeqT.lhsSubstitute(X, And(TRUE, X)).prove({B})
    # (A and B) assuming A, B via (TRUE and TRUE)
    AeqT.lhsSubstitute(X, And(X, B)).prove({A, B})
    # forall_{A | A, B | B} (A and B)
    return And(A, B).generalize((A, B), (A, B)).qed()
booleans.deriveOnDemand('conjunctionIntro', conjunctionIntroDerivation)

# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
def unfoldInBoolDerivation():
    from sets import sets, In, Singleton
    from equality import Equals
    # [A in ({TRUE} union {FALSE})] assuming inBool(A)
    AinTunionF = booleans.boolsDef.rhsSubstitute(X, In(A, X)).prove({inBool(A)})
    # (A in {TRUE}) or (A in {FALSE}) assuming inBool(A)
    AinTunionF.unfold().prove({inBool(A)})
    # A=TRUE or (A in {FALSE}) assuming inBool(A)
    sets.singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({inBool(A)})
    # A=TRUE or A=FALSE assuming inBool(A)
    conclusion = sets.singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({inBool(A)})
    # forall_{A} inBool(A) => (A=TRUE or A=FALSE)
    return Implies(inBool(A), conclusion).generalize(A).qed()
booleans.deriveOnDemand('unfoldInBool', unfoldInBoolDerivation)

# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
def foldInBoolDerivation():
    from sets import sets, In, Singleton, Union
    from equality import Equals
    # hypothesis = (A=TRUE or A=FALSE)
    hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
    # (A=TRUE) or (A in {FALSE}) assuming hypothesis
    sets.singletonDef.specialize({x:A, y:FALSE}).lhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({hypothesis})
    # (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
    sets.singletonDef.specialize({x:A, y:TRUE}).lhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({hypothesis})
    # [A in ({TRUE} union {FALSE})] assuming hypothesis
    In(A, Union(Singleton(TRUE), Singleton(FALSE))).concludeAsFolded()
    # (A in BOOLEANS) assuming hypothesis
    booleans.boolsDef.lhsSubstitute(X, In(A, X)).prove({hypothesis})
    # forall_{A} (A=TRUE or A=FALSE) => inBool(A)
    return Implies(hypothesis, inBool(A)).generalize(A).qed()
booleans.deriveOnDemand('foldInBool', foldInBoolDerivation)    
    
# forall_{A} Not(A) => [A => FALSE]
def contradictionFromNegationDerivation():
    # FALSE assuming Not(A) and A
    Not(A).equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), A})
    return Implies(Not(A), Implies(A, FALSE)).generalize(A).qed()
booleans.deriveOnDemand('contradictionFromNegation', contradictionFromNegationDerivation)

# forall_{A} (A=FALSE) => Not(A)
def notFromEqFalseDerivation():
    from equality import Equals
    # AeqF := (A=F)
    AeqF = Equals(A, FALSE)
    # Not(FALSE)
    booleans.notFalse
    # Not(A) assuming A=FALSE because Not(FALSE)
    notA = AeqF.lhsSubstitute(X, Not(X)).prove({AeqF})
    return Implies(AeqF, notA).generalize(A).qed()
booleans.deriveOnDemand('notFromEqFalse', notFromEqFalseDerivation)

# forall_{A} (FALSE=A) => Not(A)
def notFromEqFalseRevDerivation():
    from equality import Equals
    # FeqA := (F=A)
    FeqA = Equals(FALSE, A)
    # Not(A) assuming FeqA
    notA = FeqA.deriveReversed().deriveViaBooleanEquality().prove({FeqA})
    return Implies(FeqA, notA).generalize(A).qed()
booleans.deriveOnDemand('notFromEqFalseRev', notFromEqFalseRevDerivation)

# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
def notOrFromNeitherDerivation():
    # Not(A or B) = Not(F or B) assuming Not(A)
    notAorB_eq_notForB = Not(A).equateNegatedToFalse().substitution(X, Not(Or(X, B))).prove({Not(A)})
    # Not(A or B) = Not(F or F) assuming Not(A), Not(B)
    notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(Not(B).equateNegatedToFalse().substitution(X, Not(Or(FALSE, X)))).prove({Not(A), Not(B)})
    #  Not(A or B) = Not(F) assuming Not(A), Not(B)
    notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(booleans.orFF.substitution(X, Not(X))).prove({Not(A), Not(B)})
    # Not(FALSE)
    booleans.notFalse
    # Not(A or B) assuming Not(A), Not(B)
    notAorB = notAorB_eq_notF.deriveLeftViaEquivalence().prove({Not(A), Not(B)})
    # forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
    return Implies(Not(A), Implies(Not(B), notAorB)).generalize((A, B)).qed()
booleans.deriveOnDemand('notOrFromNeither', notOrFromNeitherDerivation)

# forall_{A, B | Not(A), Not(B)} (A or B) => FALSE
def orContradictionDerivation():
    # (A or B) => FALSE assuming Not(A), Not(B)
    AorB_impl_F = booleans.notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()
    return AorB_impl_F.generalize((A, B), (Not(A), Not(B))).qed()    
booleans.deriveOnDemand('orContradiction', orContradictionDerivation)

# forall_{A, B | inBool(A), Not(B)} (A or B) => A
def orImpliesLeftIfNotRightDerivation():
    # (A or B) => FALSE assuming Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: A assuming inBool(A), A or B, Not(B)
    Implies(Not(A), FALSE).deriveViaContradiction().prove({inBool(A), Or(A, B), Not(B)})
    # forall_{A, B | inBool(A), Not(B)} (A or B) => A
    return Implies(Or(A, B), A).generalize((A, B), (inBool(A), Not(B))).qed()
booleans.deriveOnDemand('orImpliesLeftIfNotRight', orImpliesLeftIfNotRightDerivation)

# forall_{A, B | Not(A), inBool(B)} (A or B) => B
def orImpliesRightIfNotLeftDerivation():    
    # (A or B) => FALSE assuming Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: B assuming inBool(B), (A or B), Not(A)
    Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), Or(A, B), Not(A)})
    # forall_{A, B | Not(A), inBool(B)} (A or B) => B
    return Implies(Or(A, B), B).generalize((A, B), (Not(A), inBool(B))).qed()
booleans.deriveOnDemand('orImpliesRightIfNotLeft', orImpliesRightIfNotLeftDerivation)

# forall_{A} A => Not(Not(A))
def doubleNegationDerivation():
    # A=TRUE assuming A
    AeqT = deriveStmtEqTrue(A)
    # [Not(A)=FALSE] assuming A=TRUE
    AeqT.substitution(X, Not(X)).applyTransitivity(booleans.notT).prove({AeqT})
    # [Not(A)=FALSE] => Not(Not(A))
    booleans.notFromEqFalse.specialize({A:Not(A)}).prove()
    # forall_{A} A => Not(Not(A))
    return Implies(A, Not(Not(A))).generalize(A).qed()
booleans.deriveOnDemand('doubleNegation', doubleNegationDerivation)

# forall_{A} A => [Not(A)=FALSE]
def eqFalseFromNegationDerivation():
    # Not(Not(A)) assuming A
    notNotA = Not(Not(A)).concludeViaDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse()).generalize(A).qed()
booleans.deriveOnDemand('eqFalseFromNegation', eqFalseFromNegationDerivation)

# forall_{A} A => [FALSE=Not(A)]
def eqFalseRevFromNegationDerivation():
    # Not(Not(A)) assuming A
    notNotA = Not(Not(A)).concludeViaDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse().deriveReversed()).generalize(A).qed()
booleans.deriveOnDemand('eqFalseRevFromNegation', eqFalseRevFromNegationDerivation)

"""
# forall_{A | inBool(A)} Not(Not(A)) => A
def fromDoubleNegationDerivation():
    # hypothesis = Not(Not(A))
    hypothesis = Not(Not(A)).state()
    # FALSE assuming Not(A), Not(Not(A))
    hypothesis.equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), hypothesis})
    # [Not(A) => FALSE] => A assuming inBool(A)
    booleans.contradictoryValidation.specialize().prove({inBool(A)})
    # inBool(A) => [Not(Not(A)) => A] via hypothetical reasoning
    return Implies(hypothesis, A).generalize(A, inBool(A)).qed()
booleans.deriveOnDemand('fromDoubleNegation', fromDoubleNegationDerivation)
"""

# forall_{A | inBool(A)} (A != FALSE) => A
def fromNotFalseDerivation():
    from equality import NotEquals
    # AnotF = (A != FALSE)
    AnotF = NotEquals(A, FALSE)
    # notAeqF = Not(A = FALSE)
    notAeqF = AnotF.unfold()
    # (A=TRUE or A=FALSE) assuming inBool(A)
    AeqT_or_AeqF = inBool(A).unfold()
    AeqT = AeqT_or_AeqF.operands[0]
    # Not(A=FALSE) and (A=TRUE or A=FALSE) assuming each
    compose(notAeqF, AeqT_or_AeqF).prove({AnotF, AeqT_or_AeqF})
    # inBool(A=TRUE)
    AeqT.deduceInBool()
    # A assuming inBool(A), Not(A=FALSE)
    AeqT_or_AeqF.deriveLeftIfNotRight().deriveViaBooleanEquality().prove({inBool(A), AnotF})
    # forall_{A | inBool(A)} Not(A=FALSE) => A
    return Implies(AnotF, A).generalize(A, inBool(A)).qed()
booleans.deriveOnDemand('fromNotFalse', fromNotFalseDerivation)

# forall_{A, B | inBool(B)} [Not(B) => Not(A)] => [A=>B] 
def transpositionFromNegatedDerivation():
    # hypothesis = [Not(B) => Not(A)]
    hypothesis = Implies(Not(B), Not(A))
    # A=FALSE assuming Not(B)=>Not(A) and Not(B)
    AeqF = Not(A).equateNegatedToFalse().prove({hypothesis, Not(B)})
    # FALSE assuming Not(B)=>Not(A), Not(B), and A
    AeqF.deriveRightViaEquivalence().prove({hypothesis, Not(B), A})
    # B assuming inBool(B), (Not(B)=>Not(A)), A
    Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), hypothesis, A})
    # [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming inBool(B)
    transpositionExpr = Implies(hypothesis, Implies(A, B)).prove({inBool(B)})
    # forall_{A, B | inBool(B)} [A => B] => [Not(B) => Not(A)]
    return transpositionExpr.generalize((A, B), inBool(B)).qed()
booleans.deriveOnDemand('transpositionFromNegated', transpositionFromNegatedDerivation)

# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
def doubleNegateConclusionDerivation():
    # Not(Not(B)) assuming B and inBool(B)
    notNotB = Not(Not(B)).concludeViaDoubleNegation()
    # [A=>B] => [A => Not(Not(B))] assuming inBool(B)
    innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
    # forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
    return innerExpr.generalize((A, B), inBool(B)).qed()
booleans.deriveOnDemand('doubleNegateConclusion', doubleNegateConclusionDerivation)

# forall_{A, B | inBool(A), inBool(B)} [Not(B) => A] => [Not(A)=>B] 
def transpositionFromNegatedHypothesisDerivation():
    # [Not(B) => Not(Not(A))] => [Not(A) => B)]  assuming inBool(B)
    toConclusion = Implies(Not(B), Not(Not(A))).transposition()
    # [Not(B) => A] => [Not(B) => Not(Not(A))] assuming inBool(A)    
    fromHyp = booleans.doubleNegateConclusion.specialize({A:Not(B), B:A}).prove({inBool(A)})
    # [Not(B) => A] => [Not(A)=>B] assuming inBool(A) and inBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | inBool(A), inBool(B)} [Not(B) => A] => [Not(A)=>B] 
    return transpositionExpr.generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('transpositionFromNegatedHypothesis', transpositionFromNegatedHypothesisDerivation)

# forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
def transpositionFromNegatedConclusionDerivation():
    from equality import Equals, NotEquals
    # inBool(B=FALSE)
    Equals(B, FALSE).deduceInBool()
    # [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using inBool(B=FALSE)
    midPointBackHalf = Implies(Not(Equals(B, FALSE)), Not(A)).transposition()
    # [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
    midPointFrontHalf = NotEquals(B, FALSE).definition().rhsStatementSubstitution(X, Implies(X, Not(A))).prove()
    # [(B != FALSE) => Not(A)] => [A => (B=FALSE)]
    midPoint = midPointFrontHalf.applySyllogism(midPointBackHalf).prove()
    # B assuming (B != FALSE) and inBool(B)
    notBeqF = NotEquals(B, FALSE)
    notBeqF.deriveViaDoubleNegation().prove({notBeqF, inBool(B)})
    # [B => Not(A)] => [(B != FALSE) => Not(A)] assuming inBool(B)
    fromHyp = Implies(Implies(B, Not(A)), Implies(notBeqF, Not(A))).prove({inBool(B)})
    # Not(B) assuming B=FALSE
    BeqF = Equals(B, FALSE)
    BeqF.deriveViaBooleanEquality().prove({BeqF})
    # [A => (B=FALSE)] => [A => Not(B)] assuming inBool(B)
    toConclusion = Implies(Implies(A, BeqF), Implies(A, Not(B))).prove({inBool(B)})
    # [B => Not(A)] => [A=>Not(B)] assuming inBool(B)
    transpositionExpr = fromHyp.applySyllogism(midPoint).applySyllogism(toConclusion).prove({inBool(B)})
    # forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
    return transpositionExpr.generalize((A, B), inBool(B)).qed()
booleans.deriveOnDemand('transpositionFromNegatedConclusion', transpositionFromNegatedConclusionDerivation)

# forall_{A, B | inBool(A), inBool(B)} [B=>A] => [Not(A) => Not(B)] 
def transpositionToNegatedDerivation():
    # [B => Not(Not(A))] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
    toConclusion = Implies(B, Not(Not(A))).transposition()
    # [B => A] => [B => Not(Not(A))] assuming inBool(A)
    fromHyp = booleans.doubleNegateConclusion.specialize({A:B, B:A}).prove({inBool(A)})
    # [B => A] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | inBool(A), inBool(B)} [B=>A] => [Not(A) => Not(B)] 
    return transpositionExpr.generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('transpositionToNegated', transpositionToNegatedDerivation)

# TRUE != FALSE
booleans.deriveOnDemand('trueNotFalse', lambda : booleans.falseNotTrue.deriveReversed().qed())

# forall_{A} A => (A != FALSE)
def notEqualsFalseDerivation():
    from equality import NotEquals
    # A=TRUE assuming A
    AeqT = deriveStmtEqTrue(A)
    # TRUE != FALSE
    booleans.trueNotFalse
    # (A != FALSE) assuming A
    AnotF = AeqT.lhsSubstitute(X, NotEquals(X, FALSE)).prove({A})
    # forall_{A} A => (A != FALSE)
    return Implies(A, AnotF).generalize(A).qed()
booleans.deriveOnDemand('notEqualsFalse', notEqualsFalseDerivation)

# inBool(TRUE)
def trueInBoolDerivation():
    from equality import Equals
    # [TRUE or FALSE] 
    booleans.orTF.deriveViaBooleanEquality().prove()
    # [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
    booleans.trueNotFalse.unfold().equateNegatedToFalse().lhsSubstitute(X, Or(TRUE, X)).prove()
    # [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
    deriveStmtEqTrue(booleans.trueEqTrue).lhsSubstitute(X, Or(X, Equals(TRUE, FALSE))).prove()
    # inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
    return inBool(TRUE).concludeAsFolded().qed()
booleans.deriveOnDemand('trueInBool', trueInBoolDerivation)

# inBool(FALSE)
def falseInBoolDerivation():
    from equality import Equals
    # [FALSE or TRUE] 
    booleans.orFT.deriveViaBooleanEquality().prove()
    # [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
    deriveStmtEqTrue(booleans.falseEqFalse).lhsSubstitute(X, Or(FALSE, X)).prove()
    # [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
    booleans.falseNotTrue.unfold().equateNegatedToFalse().lhsSubstitute(X, Or(X, Equals(FALSE, FALSE))).prove()
    # inBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
    return inBool(FALSE).concludeAsFolded().qed()
booleans.deriveOnDemand('falseInBool', falseInBoolDerivation)

# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
def unfoldForallOverBoolDerivation():
    # hypothesis = [forall_{A in BOOLEANS} P(A)]
    hypothesis = Forall(A, PofA, inBool(A))
    # TRUE in BOOLEANS, FALSE in BOOLEANS
    booleans.trueInBool, booleans.falseInBool
    # P(TRUE) and P(FALSE) assuming hypothesis
    conclusion = compose(hypothesis.specialize({A:TRUE}), hypothesis.specialize({A:FALSE})).prove({hypothesis})
    # forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
    return Implies(hypothesis, conclusion).generalize(P).qed()
booleans.deriveOnDemand('unfoldForallOverBool', unfoldForallOverBoolDerivation)

# forall_{A} A=TRUE => inBool(A)
def inBoolIfEqTrueDerivation():
    from equality import Equals
    # hypothesis = (A=TRUE)
    hypothesis = Equals(A, TRUE)
    # inBool(TRUE)
    booleans.trueInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
    # forall_{A} A=TRUE => inBool(A)
    return Implies(hypothesis, conclusion).generalize(A).qed()
booleans.deriveOnDemand('inBoolIfEqTrue', inBoolIfEqTrueDerivation)

# forall_{A} TRUE=A => inBool(A)
def inBoolIfEqTrueRevDerivation():
    from equality import Equals
    # hypothesis = (TRUE=A)
    hypothesis = Equals(TRUE, A)
    # inBool(TRUE)
    booleans.trueInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
    # forall_{A} (TRUE=A) => inBool(A)
    return Implies(hypothesis, conclusion).generalize(A).qed()
booleans.deriveOnDemand('inBoolIfEqTrueRev', inBoolIfEqTrueRevDerivation)

# forall_{A} A=FALSE => inBool(A)
def inBoolIfEqFalseDerivation():
    from equality import Equals
    # hypothesis = (A=FALSE)
    hypothesis = Equals(A, FALSE)
    # inBool(FALSE)
    booleans.falseInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
    # forall_{A} A=FALSE => inBool(A)
    return Implies(hypothesis, conclusion).generalize(A).qed()
booleans.deriveOnDemand('inBoolIfEqFalse', inBoolIfEqFalseDerivation)

# forall_{A} FALSE=A => inBool(A)
def inBoolIfEqFalseRevDerivation():
    from equality import Equals
    # hypothesis = (FALSE=A)
    hypothesis = Equals(FALSE, A)
    # inBool(FALSE)
    booleans.falseInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
    # forall_{A} (FALSE=A) => inBool(A)
    return Implies(hypothesis, conclusion).generalize(A).qed()
booleans.deriveOnDemand('inBoolIfEqFalseRev', inBoolIfEqFalseRevDerivation)

# forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
def hypotheticalDisjunctionDerivation():
    AorB = Or(A, B)
    hypothesis = And(Implies(A, C), Implies(B, C))
    ABCareBoolInOrder = [inBool(A), inBool(B), inBool(C)]
    ABCareBool = set(ABCareBoolInOrder)
    # A=>C, B=>C assuming (A=>C and B=>C)
    AimplC, _ = hypothesis.decompose()
    # Not(A) assuming inBool(A), inBool(B), (A=>C and B=>C), Not(C)
    AimplC.transpose().deriveConclusion().prove({inBool(A), inBool(C), hypothesis, Not(C)})
    # B assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    AorB.deriveRightIfNotLeft().prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # Not(TRUE) assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    deriveStmtEqTrue(C).rhsSubstitute(X, Not(X)).prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # FALSE assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    booleans.notT.deriveRightViaEquivalence().prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # Contradiction proof of C assuming (A=>C and B=>C), (A or B), inBool(A), and inBool(B)
    Implies(Not(C), FALSE).deriveViaContradiction().prove(ABCareBool | {hypothesis, AorB})
    return Implies(hypothesis, Implies(AorB, C)).generalize((A, B, C), ABCareBoolInOrder).qed()
booleans.deriveOnDemand('hypotheticalDisjunction', hypotheticalDisjunctionDerivation)

# forall_{P} [P(TRUE) and P(FALSE)] => [forall_{A in BOOLEANS} P(A)]
def foldForallOverBoolDerivation():
    from equality import Equals
    # hypothesis = [P(TRUE) and P(FALSE)]
    hypothesis = And(PofTrue, PofFalse)
    # inBool(A=TRUE), inBool(A=FALSE), inBool(P(A) = TRUE)
    AeqT = Equals(A, TRUE)
    AeqF = Equals(A, FALSE)
    PofAeqT = Equals(PofA, TRUE)
    for eqExpr in (AeqT, AeqF, PofAeqT):
        eqExpr.deduceInBool()
    # P(TRUE), P(FALSE) assuming hypothesis
    for case in hypothesis.decompose(): case.prove({hypothesis})
    # A=TRUE => P(A)=TRUE assuming hypothesis
    Implies(AeqT, deriveStmtEqTrue(AeqT.lhsSubstitute(A, PofA))).prove({hypothesis})
    # A=FALSE => P(A)=TRUE assuming hypothesis
    Implies(AeqF, deriveStmtEqTrue(AeqF.lhsSubstitute(A, PofA))).prove({hypothesis})
    # P(A) assuming hypothesis, (A in BOOLEANS)
    inBool(A).unfold().deriveCommonConclusion(PofAeqT).deriveViaBooleanEquality().prove({hypothesis, inBool(A)})
    # forall_{P} P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
    return Implies(hypothesis, PofA.generalize(A, inBool(A))).generalize(P).qed()
booleans.deriveOnDemand('foldForallOverBool', foldForallOverBoolDerivation)

# forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
def forallBoolEvalTrueDerivation():
    # P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
    folding = booleans.foldForallOverBool.specialize()
    # forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
    return Implies(folding.hypothesis, deriveStmtEqTrue(folding.deriveConclusion())).generalize(P).qed()
booleans.deriveOnDemand('forallBoolEvalTrue', forallBoolEvalTrueDerivation)

# forall_{P, Q*, R*} forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*) => forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
def forallBundlingDerivation():
    hypothesis = Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar)
    conclusion = hypothesis.specialize().specialize().generalize((xStar, yStar), (multiQ_of_xStar, multiR_of_yStar)).prove({hypothesis})
    return Implies(hypothesis, conclusion).generalize((P, multiQ, multiR)).qed()
booleans.deriveOnDemand('forallBundling', forallBundlingDerivation)

# forall_{P, Q*, R*} forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*) => forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x, y*) 
def forallUnravellingDerivation():
    hypothesis = Forall((xStar, yStar), P_of_xStar_yStar, (multiQ_of_xStar, multiR_of_yStar))
    conclusion = hypothesis.specialize().generalize(yStar, multiR_of_yStar).generalize(xStar, multiQ_of_xStar).prove({hypothesis})
    return Implies(hypothesis, conclusion).generalize((P, multiQ, multiR)).qed()
booleans.deriveOnDemand('forallUnravelling', forallUnravellingDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
def iffOverBoolImplEqDerivation():
    from equality import Equals
    # Note that proveByEval doesn't work for bundled Forall yet, 
    # but later we'll be able to do this kind of thing in one step.
    # forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
    nestedVersion = Forall(A, Forall(B, Implies(Iff(A, B), Equals(A, B)), inBool(B)), inBool(A)).proveByEval()
    # forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
    return nestedVersion.specialize().specialize().generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('iffOverBoolImplEq', iffOverBoolImplEqDerivation)

# forall_{A in booleans} A = Not(Not(A))
def doubleNegationEquivDerivation():
    # A => Not(Not(A))
    doubleNegationImplied = booleans.doubleNegation.specialize().prove()
    # Not(Not(A)) => A
    impliesDoubleNegation = booleans.fromDoubleNegation.specialize().prove()
    # [A => Not(Not(A))] in BOOLEANS if A in BOOLEANS
    doubleNegationImplied.deduceInBool().prove({inBool(A)})
    # [Not(Not(A)) => A] in BOOLEANS if A in BOOLEANS
    impliesDoubleNegation.deduceInBool().prove({inBool(A)})
    # forall_{A} A = Not(Not(A))
    return Iff(A, Not(Not(A))).concludeViaComposition().deriveEquality().generalize(A, inBool(A)).qed()
booleans.deriveOnDemand('doubleNegationEquiv', doubleNegationEquivDerivation)

# forall_{P, Q*, R*} forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*) = forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x, y*) 
def forallBundledEquivDerivation():
    # forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*) => forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
    forallBundlingSpec = booleans.forallBundling.specialize().prove()
    # forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*) => forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x, y*) 
    booleans.forallUnravelling.specialize().prove()
    # lhs = forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*)
    # rhs = forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
    lhs, rhs = forallBundlingSpec.conclusion, forallBundlingSpec.hypothesis
    # lhs in BOOLEANS, rhs in BOOLEANS
    for expr in (lhs, rhs): expr.deduceInBool().prove()
    # lhs = rhs
    equiv = Iff(lhs, rhs).concludeViaComposition().deriveEquality().prove()
    return equiv.generalize((P, multiQ, multiR)).qed()
booleans.deriveOnDemand('forallBundledEquiv', forallBundledEquivDerivation)

"""
# forall_{P, Q*, R*} [forall_{x* | Q*(x)} forall_{y* | R*(y*)} P(x*, y*) = val] => [forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*) = val]
def forallEvalBundlingDerivation(val):
    # forall_{y* | R*(y*)} P(x*, y*) => forall_{x*, y* | Q*(x), R*(y*)} P(x*, y*)
    booleans.forallBundling.specialize()
    
    hypothesis = Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar)
    conclusion = hypothesis.specialize().specialize().generalize((xStar, yStar), (multiQ_of_xStar, multiR_of_yStar)).prove({hypothesis})
    return Implies(hypothesis, conclusion).generalize((P, multiQ, multiR)).qed()
booleans.deriveOnDemand('forallEvalTrueBundling', forallEvalBundlingDerivation(TRUE))
booleans.deriveOnDemand('forallEvalFalseBundling', forallEvalBundlingDerivation(FALSE))
"""

"""
# forall_{P, Q*} [forall_{x* | Q*(x*)} P(TRUE, x*) and forall_{x* | Q(x*)} P(FALSE, x*)] => {[forall_{A in BOOLEANS, x* | Q(x*)} P(A, x*)] = TRUE}
def forallBoolEtcEvalTrueDerivation():
    P_of_T_xStar = Operation(P, (TRUE, xStar))
    P_of_F_xStar = Operation(P, (FALSE, xStar))
    P_of_A_xStar = Operation(P, (A, xStar))
    # hypothesis = [forall_{x* | Q*(x*)} P(TRUE, x*) and forall_{x* | Q*(x*)} P(FALSE, x*)]
    hypothesis = And(Forall(xStar, P_of_T_xStar, multiQ_of_xStar), Forall(xStar, P_of_F_xStar, multiQ_of_xStar))
    # unbundled = [forall_{A in BOOLEANS} forall_{x* | Q*(x*)} P(A, x)] assuming hypothesis
    unbundled = Forall(A, Forall(xStar, P_of_A_xStar, multiQ_of_xStar), inBool(A)).concludeAsFolded().prove({hypothesis})
    # forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x) = TRUE assuming hypothesis
    conclusion = deriveStmtEqTrue(unbundled.deriveBundled()).prove({hypothesis})
    # forall_{P} [forall_{x* | Q*(x*)} P(TRUE, x*) and forall_{x* | Q(x*)} P(FALSE, x*)] => {[forall_{A in BOOLEANS, x* | Q(x*)} P(A, x*)] = TRUE}
    return Implies(hypothesis, conclusion).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('forallBoolEtcEvalTrue', forallBoolEtcEvalTrueDerivation)
"""
  
# forall_{P, Q*} [forall_{x* | Q*(x*)} P(x*)] = [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
def forallEqTrueEquivDerivation():
    from equality import Equals
    # forallPx = [forall_{x* | Q*(x*)} P(x*)]
    forallPx = Forall(xStar, P_of_xStar, multiQ_of_xStar)
    # forallPxEqT = [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
    forallPxEqT = Forall(xStar, Equals(P_of_xStar, TRUE), multiQ_of_xStar)
    # forallPxEqT assuming forallPx
    deriveStmtEqTrue(forallPx.specialize()).generalize(xStar, multiQ_of_xStar).prove({forallPx})
    # forallPx assuming forallPxEqT
    forallPxEqT.specialize().deriveViaBooleanEquality().generalize(xStar, multiQ_of_xStar).prove({forallPxEqT})
    # [forall_{x* | Q*(x*)} P(x*)] <=> [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
    iffForalls = Iff(forallPx, forallPxEqT).concludeViaComposition().prove()
    # forallPx in BOOLEANS, forallPxEqT in BOOLEANS
    for expr in (forallPx, forallPxEqT):
        expr.deduceInBool()
    # forall_{P, Q*} [forall_{x* | Q*(x*)} P(x*)] = [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
    return iffForalls.deriveEquality().generalize((P, multiQ)).qed()
booleans.deriveOnDemand('forallEqTrueEquiv', forallEqTrueEquivDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A => B) in BOOLEANS                                                                                                        
def implicationClosureDerivation():
    from equality import Equals
    # [(A=>B) = TRUE] or [(A=>B) = FALSE] assuming A, B in BOOLEANS
    Forall((A, B), Or(Equals(Implies(A, B), TRUE), Equals(Implies(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A => B) in BOOLEANS  
    return inBool(Implies(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('implicationClosure', implicationClosureDerivation)


# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) in BOOLEANS                                                                                                        
def iffClosureDerivation():
    from equality import Equals
    # [(A<=>B) = TRUE] or [(A<=>B) = FALSE] assuming A, B in BOOLEANS
    Forall((A, B), Or(Equals(Iff(A, B), TRUE), Equals(Iff(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A <=> B) in BOOLEANS  
    return inBool(Iff(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('implicationClosure', implicationClosureDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A and B) in BOOLEANS                                                                                                        
def conjunctionClosureDerivation():
    from equality import Equals
    # [(A and B) = TRUE] or [(A and B) = FALSE] assuming A, B in BOOLEANS
    Forall((A, B), Or(Equals(And(A, B), TRUE), Equals(And(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A and  B) in BOOLEANS  
    return inBool(And(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('conjunctionClosure', conjunctionClosureDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A or B) in BOOLEANS                                                                                                        
def disjunctionClosureDerivation():
    from equality import Equals
    # [(A or B) = TRUE] or [(A or B) = FALSE] assuming A, B in BOOLEANS
    Forall((A, B), Or(Equals(Or(A, B), TRUE), Equals(Or(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A or  B) in BOOLEANS  
    return inBool(Or(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))).qed()
booleans.deriveOnDemand('disjunctionClosure', disjunctionClosureDerivation)

# forall_{A in BOOLEANS} Not(A) in BOOLEANS                                                                                                        
def negationClosureDerivation():
    from equality import Equals
    # Not(A) = TRUE or Not(A) = FALSE assuming A in BOOLEANS
    Forall(A, Or(Equals(Not(A), TRUE), Equals(Not(A), FALSE)), inBool(A)).proveByEval().specialize().prove({inBool(A)})
    # forall_{A in BOOLEANS} Not(A) in BOOLEANS  
    return inBool(Not(A)).concludeAsFolded().generalize(A, inBool(A)).qed()
booleans.deriveOnDemand('negationClosure', negationClosureDerivation)

# forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                            
def hypotheticalContradictionDerivation():
    # inBool(Not(A)) assuming inBool(A)    
    Not(A).deduceInBool().prove({inBool(A)})
    # [Not(Not(A)) => FALSE] => Not(A) assuming inBool(A)                                     
    booleans.contradictoryValidation.specialize({A:Not(A)}).prove({inBool(A)})
    # A assuming Not(Not(A)) and inBool(A)                                                    
    Not(Not(A)).deriveViaDoubleNegation().prove({inBool(A), Not(Not(A))})
    # forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                        
    return Implies(Implies(A, FALSE), Not(A)).generalize(A, inBool(A)).qed()
booleans.deriveOnDemand('hypotheticalContradiction', hypotheticalContradictionDerivation)    

# forall_{P, Q*} [notexists_{x* | Q*(x*)} P(x*) = forall_{x* | Q*(x*)} (P(x*) != TRUE)]
def existsDefNegationDerivation():
    from equality import NotEquals
    # [exists_{x* | Q*(x*)} P(x*)] = not(forall_{x* | Q*(x*)} (P(x*) != TRUE))
    existsDefSpec = booleans.existsDef.specialize().prove()
    # notexists_{x* | Q*(x*)} P(x*) = not[exists_{x* | Q*(x*)} P(x*)]
    notExistsDefSpec = booleans.notExistsDef.specialize().prove()
    # rhs = forall_{x* | Q*(x*)} (P(x*) != TRUE)
    rhs = Forall(xStar, NotEquals(P_of_xStar, TRUE), multiQ_of_xStar)
    # [forall_{x* | Q*(x*)} (P(x*) != TRUE)] in BOOLEANS
    rhs.deduceInBool().prove()
    # not(not(forall_{x* | Q*(x*)} (P(x*) != TRUE))) = forall_{x* | Q*(x*)} (P(x*) != TRUE))
    doubleNegatedForall = Not(Not(rhs)).deduceDoubleNegationEquiv().deriveReversed().prove()
    # notexists_{x* | Q*(x*)} P(x*) = forall_{x* | Q*(x*)} (P(x*) != TRUE))
    equiv = notExistsDefSpec.applyTransitivity(existsDefSpec.substitution(X, Not(X))).applyTransitivity(doubleNegatedForall).prove()
    # forall_{P, Q*} [notexists_{x* | Q*(x*)} P(x*) = forall_{x* | Q*(x*)} (P(x*) != TRUE)]
    return equiv.generalize((P, multiQ)).qed()
booleans.deriveOnDemand('existsDefNegation', existsDefNegationDerivation)    

# forall_{P, Q*} NotExists_{x* | Q*(x*)} P(x*) => Not(Exists_{x* | Q*(x*)} P(x*))
def notExistsUnfoldingDerivation():
    return booleans.notExistsDef.specialize().rightImplViaEquivalence().generalize((P, multiQ)).qed()
booleans.deriveOnDemand('notExistsUnfolding', notExistsUnfoldingDerivation)

# forall_{P, Q*} Not(Exists_{x* | Q*(x*)} P(x*)) => NotExists_{x* | Q*(x*)} P(x*)
def notExistsFoldingDerivation():
    return booleans.notExistsDef.specialize().leftImplViaEquivalence().generalize((P, multiQ)).qed()
booleans.deriveOnDemand('notExistsFolding', notExistsFoldingDerivation)

# forall_{P, Q*} [exists_{x* | Q*(x*)} P(x*)] in BOOLEANS
def existsInBoolDerivation():
    from equality import Equals
    # exists_{x* | Q*(x*)} P(x*) = not(forall_{x* | Q*(x*)} P(x*) != TRUE)
    existsDefSpec = booleans.existsDef.specialize().prove()
    # [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = TRUE] or [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = FALSE]
    rhsTrue, rhsFalse = existsDefSpec.rhs.deduceInBool().unfold().prove().operands
    # exists_{x* | Q*(x*)} P(x*) in BOOLEANS assuming [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = TRUE]
    existsInBoolSpec = rhsTrue.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsTrue})
    # exists_{x* | Q*(x*)} P(x*) in BOOLEANS assuming [not(forall_{x* | Q*(x*)} P(x*) != TRUE) = FALSE]
    rhsFalse.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsFalse})
    # deduce rhsTrue, rhsFals, existsInBoolSpec all in BOOLEANS
    for expr in (rhsTrue, rhsFalse, existsInBoolSpec): expr.deduceInBool()
    # forall_{P, Q*} exists_{x* | Q*(x*)} P(x*) in BOOLEANS
    return Or(rhsTrue, rhsFalse).deriveCommonConclusion(existsInBoolSpec).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('existsInBool', existsInBoolDerivation)

# forall_{P, Q*} forall_{x* | Q*(x*)} [P(x*) => exists_{y* | Q(y*)} P(y*)]
def existenceByExampleDerivation():
    from equality import NotEquals
    # neverPy = [forall_{y* | Q*(y*)} (P(y*) != TRUE)]
    neverPy = Forall(yStar, NotEquals(P_of_yStar, TRUE), multiQ_of_yStar)
    # (P(x*) != TRUE) assuming Q*(x*), neverPy
    neverPy.specialize({yStar:xStar}).prove({multiQ_of_xStar, neverPy})
    # (TRUE != TRUE) assuming Q*(x*), P(x*), neverPy
    trueNotEqTrue = deriveStmtEqTrue(P_of_xStar).rhsSubstitute(X, NotEquals(X, TRUE)).prove({multiQ_of_xStar, P_of_xStar, neverPy})
    # FALSE assuming Q*(x*), P(x*), neverPy
    trueNotEqTrue.evaluate().deriveContradiction().deriveConclusion().prove({multiQ_of_xStar, P_of_xStar, neverPy})
    # [forall_{y* | Q*(y*)} (P(y*) != TRUE)] in BOOLEANS
    neverPy.deduceInBool().prove()
    # Not(forall_{y* | Q*(y*)} (P(y*) != TRUE) assuming Q*(x*), P(x*)
    Implies(neverPy, FALSE).deriveViaContradiction().prove({multiQ_of_xStar, P_of_xStar})
    # exists_{y* | Q*(y*)} P(y*) assuming Q*(x*), P(x*)
    existence = booleans.existsDef.specialize({xStar:yStar}).deriveLeftViaEquivalence().prove({multiQ_of_xStar, P_of_xStar})
    # forall_{P, Q*} forall_{x* | Q*(x*)} [P(*x) => exists_{y* | Q*(y*)} P(y*)]
    return Implies(P_of_xStar, existence).generalize(xStar, multiQ_of_xStar).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('existenceByExample', existenceByExampleDerivation)

# forall_{P, Q*} [exists_{x* | Q*(x*)} Not(P(x*))] => [Not(forall_{x* | Q*(x*)} P(x*)]
def existsNotImpliesNotForallDerivation():
    from equality import NotEquals
    # existsNot = [exists_{x* | Q*(x*)} Not(P(x*))]
    existsNot = Exists(xStar, Not(P_of_xStar), multiQ_of_xStar)
    # [Not(forall_{x* | Q(x*)} Not(P(x*)) != TRUE] assuming existsNot
    booleans.existsDef.specialize({Operation(P, xStar):Not(P_of_xStar)}).deriveRightViaEquivalence().prove({existsNot})
    # forall_{x* | Q(x*)} P(x*)
    forallPx = Forall(xStar, P_of_xStar, multiQ_of_xStar)
    # forall_{x* | Q(x*)} Not(P(x*)) != TRUE
    forallNotPxNotTrue = Forall(xStar, NotEquals(Not(P_of_xStar), TRUE), multiQ_of_xStar)
    # forallPx in BOOLEANS, forallNotPxNotTrue in BOOLEANS
    for expr in (forallPx, forallNotPxNotTrue):
        expr.deduceInBool().prove()
    # Not(TRUE) != TRUE
    NotEquals(Not(TRUE), TRUE).proveByEval()
    # forallNotPxNotTrue assuming forallPx, Q*(x*)
    deriveStmtEqTrue(forallPx.specialize()).lhsStatementSubstitution(X, NotEquals(Not(X), TRUE)).deriveConclusion().generalize(xStar, multiQ_of_xStar).prove({forallPx})
    # Not(forallNotPxNotTrue) => Not(forallPx)
    Implies(forallPx, forallNotPxNotTrue).transpose().prove()
    # forall_{P, Q*} [exists_{x* | Q*(x*)} Not(P(x*))] => [Not(forall_{x* | Q*(x*)} P(x*)]
    return Implies(existsNot, Not(forallPx)).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('existsNotImpliesNotForall', existsNotImpliesNotForallDerivation)

# forall_{P, Q*} forall_{x* | Q*(x*)} P(x*) => NotExists_{x* | Q*(x*)} Not(P(x*))
def forallImpliesNotExistsNotDerivation():
    # hypothesis = forall_{x* | Q*(x*)} P(x*)
    hypothesis = Forall(xStar, P_of_xStar, multiQ_of_xStar)
    # [exists_{x* | Q*(x*)} Not(P(x*))] => [Not(forall_{x* | Q*(x*)} P(x*)]
    existsNotImpliesNotForallSpec = booleans.existsNotImpliesNotForall.specialize().prove()
    # exists_{x* | Q*(x*)} Not(P(x*)) in BOOLEANS
    existsNotImpliesNotForallSpec.hypothesis.deduceInBool()
    # forall_{x* | Q*(x*)} P(x*) in BOOLEANS
    existsNotImpliesNotForallSpec.conclusion.operand.deduceInBool()
    # NotExists_{x* | Q*(x*)} Not(P(x*))
    conclusion = existsNotImpliesNotForallSpec.transpose().deriveConclusion().deriveNotExists().prove({hypothesis})
    # forall_{P, Q*} NotExists_{x* | Q*(x*)} Not(P(x*)) => forall_{x* | Q*(x*)} P(x*)
    return Implies(hypothesis, conclusion).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('forallImpliesNotExistsNot', forallImpliesNotExistsNotDerivation)

# forall_{P} [(P(TRUE) = PofTrueVal) and (P(FALSE) = PofFalseVal)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}, assuming PofTrueVal=FALSE or PofFalseVal=FALSE
def forallBoolEvalFalseDerivation(PofTrueVal, PofFalseVal):
    from equality import Equals
    # hypothesis = [P(TRUE) = PofTrueVal] and [P(FALSE) in PofFalseVal]
    hypothesis = And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal))
    # P(TRUE) in BOOLEANS assuming hypothesis
    hypothesis.deriveLeft().inBoolViaBooleanEquality().prove({hypothesis})
    # P(FALSE) in BOOLEANS assuming hypothesis
    hypothesis.deriveRight().inBoolViaBooleanEquality().prove({hypothesis})
    # forall_{A in BOOLEANS} P(A) in BOOLEANS assuming hypothesis
    Forall(A, inBool(PofA), inBool(A)).concludeAsFolded().prove({hypothesis})
    if PofTrueVal == FALSE:
        # Not(P(TRUE)) assuming hypothesis
        hypothesis.deriveLeft().deriveViaBooleanEquality().prove({hypothesis})
        example = TRUE
        # TRUE in BOOLEANS
        booleans.trueInBool
    elif PofFalseVal == FALSE:
        # Not(P(FALSE)) assuming hypothesis
        hypothesis.deriveRight().deriveViaBooleanEquality().prove({hypothesis})
        example = FALSE    
        # FALSE in BOOLEANS
        booleans.trueInBool
    # [forall_{A in BOOLEANS} P(A)] = FALSE assuming hypothesis
    conclusion = Exists(A, Not(PofA), inBool(A)).concludeViaExample(example).deriveNegatedForall().equateNegatedToFalse().prove({hypothesis})
    # forall_{P} [(P(TRUE) = FALSE) and (P(FALSE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, conclusion).generalize(P).qed()
booleans.deriveOnDemand('forallBoolEvalFalseViaFF', lambda : forallBoolEvalFalseDerivation(FALSE, FALSE))
booleans.deriveOnDemand('forallBoolEvalFalseViaFT', lambda : forallBoolEvalFalseDerivation(FALSE, TRUE))
booleans.deriveOnDemand('forallBoolEvalFalseViaTF', lambda : forallBoolEvalFalseDerivation(TRUE, FALSE))


"""
# forall_{P, Q*} [{forall_{x* | Q*(x*)} P(TRUE, x*)} = PofTrueVal and {forall_{x* | Q(x*)} P(FALSE, x*)} = PofFalseVal] => {[forall_{A in BOOLEANS, x* | Q(x*)} P(A, x*)] = FALSE}
def forallBoolEtcEvalFalseDerivation(PofTrueVal, PofFalseVal, forallBoolEvalFalseViaXX):
    from equality import Equals
    P_of_T_xStar = Operation(P, (TRUE, xStar))
    P_of_F_xStar = Operation(P, (FALSE, xStar))
    P_of_A_xStar = Operation(P, (A, xStar))
    # [{forall_{x* | Q*(x*)} P(TRUE, x*)} = PofTrueVal and {forall_{x* | Q(x*)} P(FALSE, x*)} = PofFalseVal] => {[forall_{A in BOOLEANS} forall_{x* | Q(x*)} P(A, x*)] = FALSE}
    nestedVersion = forallBoolEvalFalseViaXX.specialize({Operation(P, A): Forall(xStar, P_of_A_xStar, multiQ_of_xStar)}).prove()
    # hypothesis = {forall_{x* | Q*(x*)} P(TRUE, x*)} = PofTrueVal and {forall_{x* | Q(x*)} P(FALSE, x*)} = forall_{x* | Q*(x*)} P(TRUE, x*)} = PofFalseVal
    hypothesis = nestedVersion.hypothesis
    # [forall_{A in BOOLEANS} forall_{x* | Q(x*)} P(A, x*)] => FALSE, assuming hypothesis
    nestedVersion.deriveConclusion().deriveContradiction().prove({hypothesis})
    # negatedConclusion = [forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x*)]
    negatedConclusion = Forall((A, xStar), P_of_A_xStar, (inBool(A), multiQ_of_xStar))
    
    
    # [forall_{x* | Q*(x*)} P(TRUE, x*)] in BOOLEANS, assuming hypothesis
    hypothesis.deriveLeft().inBoolViaBooleanEquality().prove({hypothesis})
    # [forall_{x* | Q*(x*)} P(FALSE, x*)] in BOOLEANS, assuming hypothesis
    hypothesis.deriveRight().inBoolViaBooleanEquality().prove({hypothesis})

    # forall_{x* | Q*(x*)} [P(TRUE, x*) in BOOLEANS], assuming hypothesis   ??
    # forall_{x* | Q*(x*)} [P(FALSE, x*) in BOOLEANS], assuming hypothesis   ??

    
    # [forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x*)] in BOOLEANS, assuming hypothesis
    inBool(negatedConclusion)

    
    # forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x*) in BOOLEANS, assuming hypothesis    
    
    # [forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x*)] in BOOLEANS, assuming hypothesis
    negatedConclusion.deduceInBool().prove({hypothesis})
    
    
    # [forall_{A in BOOLEANS} forall_{x* | Q(x*)} P(A, x*)] given negatedConclusion
    negatedConclusion.deriveUnravelled(A, xStar).prove({negatedConclusion})
    # [forall_{A in BOOLEANS, x* | Q*(x*)} P(A, x*)] = FALSE given hypothesis
    conclusion = Implies(negatedConclusion, FALSE).deriveViaContradiction().equateNegatedToFalse().prove({hypothesis})
    # forall_{P, Q*} [{forall_{x* | Q*(x*)} P(TRUE, x*)} = PofTrueVal and {forall_{x* | Q(x*)} P(FALSE, x*)} = PofFalseVal] => {[forall_{A in BOOLEANS, x* | Q(x*)} P(A, x*)] = FALSE}
    return Implies(hypothesis, conclusion).generalize((P, multiQ)).qed()
booleans.deriveOnDemand('forallBoolEtcEvalFalseViaFF', lambda : forallBoolEtcEvalFalseDerivation(FALSE, FALSE, booleans.forallBoolEvalFalseViaFF))
booleans.deriveOnDemand('forallBoolEtcEvalFalseViaFT', lambda : forallBoolEtcEvalFalseDerivation(FALSE, TRUE, booleans.forallBoolEvalFalseViaFT))
booleans.deriveOnDemand('forallBoolEtcEvalFalseViaTF', lambda : forallBoolEtcEvalFalseDerivation(TRUE, FALSE, booleans.forallBoolEvalFalseViaTF))
"""