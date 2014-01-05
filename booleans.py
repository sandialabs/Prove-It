from proveItCore import *
from genericOperations import *

A = Variable('A')
B = Variable('B')
C = Variable('C')
P = Variable('P')
Q = Variable('Q')
x = Variable('x')
y = Variable('y')
Px = Operation(P, [x])
Qx = Operation(Q, [x])
Qy = Operation(Q, [y])
Py = Operation(P, [y])
PofA = Operation(P, [A])
X = Variable('X')
    
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
        _x = operation.operands[0]
        _y = operation.operands[1]
        operator = operation.operator
        if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
            evaluation = baseEvalFn(_x, _y)
        elif (_x == TRUE or _x == FALSE):
            _b = _y.evaluate().rhs
            _c = baseEvalFn(_x, _b).rhs
            dummyVar = _x.safeDummyVar() # var that isn't in _x
            _f = Function(operation.remake(operator, [_x, dummyVar]), [dummyVar])
            evaluation = equality.unaryEvaluation.specialize({f:_f, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
        elif (_y == TRUE or _y == FALSE):
            _a = _x.evaluate().rhs
            _c = baseEvalFn(_a, _y).rhs
            dummyVar = _y.safeDummyVar() # var that isn't in _y
            _f = Function(operation.remake(operator, [dummyVar, _y]), [dummyVar])
            evaluation = equality.unaryEvaluation.specialize({f:_f, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
        else:
            xEval = _x.evaluate()
            yEval = _y.evaluate()
            compose(xEval, yEval)
            _a, _b = xEval.rhs, yEval.rhs 
            _c = baseEvalFn(_a, _b).rhs
            _f = Function(operation.remake(operator, [a, b]), [a, b])
            # f(_x, _y) = _c
            evaluation = equality.binaryEvaluation.specialize({f:_f, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
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
        
        # forall_{P, Q} [exists_{x | Q(x)} P(x) <=> Not(forall_{x | Q(x)} P(x) != TRUE)]
        self.existsDef = self.stateAxiom(Forall([P], Iff(Exists([x], Px, [Qx]), Not(Forall([x], NotEquals(Px, TRUE), [Qx])))))
        
        # forall_{P, Q} [forall_{x | Q(x)} inBool(P(x)) => inBool(forall_{x | Q(x)} P(x))]
        self.forallBooleanClosure = self.stateAxiom(Forall([P, Q], Implies(Forall([x], inBool(Px), [Qx]), inBool(Forall([x], Px, [Qx])))))

        # forall_{P, Q} [forall_{x | Q(x)} inBool(P(x)) => inBool(exists_{x | Q(x)} P(x))]
        self.existsBooleanClosure = self.stateAxiom(Forall([P, Q], Implies(Forall([x], inBool(Px), [Qx]), inBool(Exists([x], Px, [Qx])))))
            
        # Truth table for NOT
        self.notF = self.stateAxiom(Equals(Not(FALSE), TRUE))
        self.notT = self.stateAxiom(Equals(Not(TRUE), FALSE))
        
        # Further defining property of NOT needed in addition to the truth table
        # because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.
        
        # forall_{A} not(A) => [A=FALSE]
        self.notImpliesEqFalse = self.stateAxiom(Forall([A], Implies(Not(A), Equals(A, FALSE))))
        
        # Truth table for AND
        self.andTT = self.stateAxiom(Equals(And(TRUE, TRUE), TRUE))
        self.andTF = self.stateAxiom(Equals(And(TRUE, FALSE), FALSE))
        self.andFT = self.stateAxiom(Equals(And(FALSE, TRUE), FALSE))
        self.andFF = self.stateAxiom(Equals(And(FALSE, FALSE), FALSE))
        
        # Further defining properties of AND needed in addition to the truth table
        # because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE.
        
        # forall_{A, B} A and B => A
        self.andImpliesLeft = self.stateAxiom(Forall([A, B], Implies(And(A, B), A)))
        # forall_{A, B} A and B => B
        self.andImpliesRight = self.stateAxiom(Forall([A, B], Implies(And(A, B), B)))
        
        
        # Truth table for OR
        self.orTT = self.stateAxiom(Equals(Or(TRUE, TRUE), TRUE))
        self.orTF = self.stateAxiom(Equals(Or(TRUE, FALSE), TRUE))
        self.orFT = self.stateAxiom(Equals(Or(FALSE, TRUE), TRUE))
        self.orFF = self.stateAxiom(Equals(Or(FALSE, FALSE), FALSE))
        
        # forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
        self.iffDef = self.stateAxiom(Forall([A, B], Equals(Iff(A, B), And(Implies(A, B), Implies(B, A)))))
        
        # forall_{A} A => (A = TRUE)
        self.eqTrueIntro = self.stateAxiom(Forall([A], Implies(A, Equals(A, TRUE))))
        # forall_{A} (A = TRUE) => A
        self.eqTrueElim = self.stateAxiom(Forall([A], Implies(Equals(A, TRUE), A)))
        
        # forall_{A | Not(A=T)} Not(TRUE => A)
        self.falseImplication = self.stateAxiom(Forall([A], Not(Implies(TRUE, A)), [NotEquals(A, TRUE)]))
        
        # forall_{A | inBool(A)} [Not(A) => FALSE] => A
        self.hypotheticalContraNegation = self.stateAxiom(Forall([A], Implies(Implies(Not(A), FALSE), A), [inBool(A)]))
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
NONCONDITION = booleans.addLiteral('NONCONDITION') # for unconditional quantifiers
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
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        instanceFn = Function(forallStmt.instanceExpression, [forallStmt.instanceVar])
        trueInstance = forallStmt.instanceExpression.substituted(SubstitutionMap({forallStmt.instanceVar:TRUE}))
        falseInstance = forallStmt.instanceExpression.substituted(SubstitutionMap({forallStmt.instanceVar:FALSE}))
        if trueInstance == TRUE and falseInstance == FALSE:
            # special case of Forall_{A in BOOLEANS} A
            booleans.falseEqFalse # FALSE = FALSE
            evaluation = booleans.forallBoolEvalFalseViaFalse.specialize({P:instanceFn}).deriveConclusion()
        else:
            evalTrueInstance = trueInstance.evaluate()
            evalFalseInstance = falseInstance.evaluate()
            if isinstance(evalTrueInstance, Equals) and evalTrueInstance.rhs == FALSE:
                evaluation = booleans.forallBoolEvalFalseViaTrue.specialize({P:instanceFn}).deriveConclusion()
            elif isinstance(evalFalseInstance, Equals) and evalFalseInstance.rhs == FALSE:
                evaluation = booleans.forallBoolEvalFalseViaFalse.specialize({P:instanceFn}).deriveConclusion()
            elif isinstance(evalTrueInstance, Equals) and isinstance(evalFalseInstance, Equals):
                if evalTrueInstance.rhs == TRUE and evalFalseInstance.rhs == TRUE:
                    compose(evalTrueInstance.deriveViaBooleanEquality(), evalFalseInstance.deriveViaBooleanEquality())
                    evaluation = booleans.forallBoolEvalTrue.specialize({P:instanceFn}).deriveConclusion()
        return evaluation
    
    def unfoldForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from sets import In
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        return booleans.unfoldForallOverBool.specialize({P:Function(forallStmt.instanceExpression, [forallStmt.instanceVar]), A:forallStmt.instanceVar}).deriveConclusion().check({forallStmt})

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
        folding = booleans.foldForallOverBool.specialize({P:Function(forallStmt.instanceExpression, [forallStmt.instanceVar]), A:forallStmt.instanceVar})
        folding.hypothesis.concludeViaComposition()
        return folding.deriveConclusion()

BOOLEANS = booleans.addLiteral(literal = BooleanSet())

    
class Forall(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=tuple()):
        '''
        Nest Forall OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, FORALL, lambda iVars, iExpr, conds: Forall(iVars, iExpr, conds), instanceVars, instanceExpression, conditions, NONCONDITION)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'forall'
        elif formatType == MATHML:
            return '<mo>&#x2200;</mo>'

    def implicitInstanceVar(self):
        '''
        If the condition is that the instance variable is in some set, then
        the instance variable is implicit (stating the condition indicates
        the instance variable).
        '''
        from sets import In
        return isinstance(self.condition, In) and self.condition.element == self.instanceVar

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == FORALL:
            return Forall([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)

    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.
        '''
        specialized = Expression.specialize(self, subMap)
        if conditionAsHypothesis and self.condition != NONCONDITION:
            return Implies(self.condition, specialized).check({self})
        return specialized
    
    def instanceSubstitution(self, operatorOverInstance):
        '''
        From forall_{x | Q(x)} f(x) = g(x) and given an Upsilon (operator over instances), 
        derive and return Upsilon_{x | Q(x)} f(x) = Upsilon_{x | Q(x)} g(x)
        '''
        from equality import equality, Equals, f, g, Upsilon
        assert isinstance(self.instanceExpression, Equals)
        fSub = Function(self.instanceExpression.lhs, [self.instanceVar])
        gSub = Function(self.instanceExpression.rhs, [self.instanceVar])
        Qsub = Function(self.condition, [self.instanceVar])
        operationOverInstances = OperationOverInstances(operatorOverInstance, self.instanceVar, self.instanceExpression, self.condition)
        # [Upsilon_{x | Q(x)} f(x)] = [Upsilon_{x | Q(x)} g(x)]
        return equality.instanceSubstitution.specialize({f:fSub, g:gSub, Q:Qsub, Upsilon:operatorOverInstance}).deriveConclusion().check({self, operationOverInstances})

    def unfold(self):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the condition of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        return self.condition.unfoldForall(self)
        
    def concludeAsFolded(self):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the condition of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        return self.condition.foldAsForall(self)

    def evaluate(self):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        return booleans.evaluate(self, lambda : self.condition.evaluateForall(self))    

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        possibly through recursive deduceInBool method calls.
        '''
        # forall_{x | Q(x)} inBool(P(x)) => inBool(forall_{x | Q(x)} P(x)), with proper Q and P
        booleans.forallBooleanClosure.specialize({P:Function(self.instanceExpression, [self.instanceVar]), Q:Function(self.condition, [self.instanceVar]), x:self.instanceVar}).check()
        # deduce forall_{x | Q(x)} inBool(P(x)) via recursion
        prerequisite = booleans.deduceInBool(self.instanceExpression).generalize([self.instanceVar], [self.condition])
        # inBool(forall_{x | Q(x)} P(x))
        return inBool(self).check({prerequisite})    

class Exists(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=tuple()):
        '''
        Nest Exists OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, EXISTS, lambda iVars, iExpr, conds: Exists(iVars, iExpr, conds), instanceVars, instanceExpression, conditions, NONCONDITION)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'exist'
        elif formatType == MATHML:
            return '<mo>&#x2203;</mo>'

    def implicitInstanceVar(self):
        '''
        If the condition is that the instance variable is in some set, then
        the instance variable is implicit (stating the condition indicates
        the instance variable).
        '''
        from sets import In
        return isinstance(self.condition, In) and self.condition.element == self.instanceVar

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == EXISTS:
            return Exists([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)  
        
    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{y | Q(x)} P(y)] from P(x), where x is the given exampleInstance.
        '''
        # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
        return booleans.existenceByExample.specialize({P:Function(self.instanceExpression, [self.instanceVar]), Q:Function(self.condition, [self.instanceVar]), x:exampleInstance, y:self.instanceVar}).deriveConclusion()       

    def unfold(self, assumeBoolStmts=True):
        '''
        If assumeBoolStmts is True, then:
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)) assuming 
        forall_{x | Q(x)} [P(x) in BOOLEANS].
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} Not(P(x))) assuming
        forall_{x | Q(x)} [P(x) in BOOLEANS].
        If assumeBoolStmts is False, from [exists_{x | Q(x)} P(x)], derive and return
        Not(forall_{x | Q(x)} P(x) != TRUE).
        '''
        Qfn = Function(self.condition, [self.instanceVar])
        if assumeBoolStmts:
            if isinstance(self.instanceExpression, Not):
                Pfn = Function(self.instanceExpression.operand, [self.instanceVar])
                assumption = Forall([self.instanceVar], inBool(self.instanceExpression.operand), [self.condition])
                return booleans.existenceOverNegated.specialize({P:Pfn, Q:Qfn, x:self.instanceVar}).deriveConclusion().deriveRight().check({self, assumption})
            else:
                Pfn = Function(self.instanceExpression, [self.instanceVar])
                assumption = Forall([self.instanceVar], inBool(self.instanceExpression), [self.condition])
                return booleans.existenceOverBoolStmts.specialize({P:Pfn, Q:Qfn, x:self.instanceVar}).deriveConclusion().deriveRight().check({self, assumption})
        return booleans.existsDef.specialize({P:Pfn, Q:Qfn, x:self.instanceVar}).deriveRight().check({self})
    
    def concludeAsFolded(self, assumeBoolStmts=True):
        '''
        If assumeBoolStmts is True, then:
        Conclude and return [exists_{x | Q(x)} Not(P(x))] from Not(forall_{x | Q(x)} P(x)) assuming 
        forall_{x | Q(x)} [P(x) in BOOLEANS],
        or conclude and return [exists_{x | Q(x)} P(x)] from Not(forall_{x | Q(x)} Not(P(x))) assuming
        forall_{x | Q(x)} [P(x) in BOOLEANS].
        If assumeBoolStmts is False, conclude and return [exists_{x | Q(x)} P(x)] from
        Not(forall_{x | Q(x)} P(x) != TRUE).
        '''
        Pfn = Function(self.instanceExpression, [self.instanceVar])
        Qfn = Function(self.condition, [self.instanceVar])
        if assumeBoolStmts:
            assumption = Forall([self.instanceVar], inBool(self.instanceExpression), [self.condition])
            if isinstance(self.instanceExpression, Not):
                specialized = booleans.existenceOverNegated.specialize({P:Pfn, Q:Qfn, x:self.instanceVar}).deriveConclusion()
            else:
                specialized = booleans.existenceOverBoolStmts.specialize({P:Pfn, Q:Qfn, x:self.instanceVar}).deriveConclusion()
            return specialized.deriveLeft().check({specialized.B, assumption})
        specialized = booleans.existsDef.specialize({P:Pfn, Q:Qfn, x:self.instanceVar})
        return specialized.deriveLeft().check({specialized.B})

    def deduceInBool(self):
        '''
        Derive and return that this exists expression is in the set of BOOLEANS,
        possibly through recursive deduceInBool method calls.
        '''
        # forall_{x | Q(x)} inBool(P(x)) => inBool(exists_{x | Q(x)} P(x)), with proper Q and P
        booleans.existsBooleanClosure.specialize({P:Function(self.instanceExpression, [self.instanceVar]), Q:Function(self.condition, [self.instanceVar]), x:self.instanceVar})
        # deduce forall_{x | Q(x)} inBool(P(x)) via recursion
        prerequisite = booleans.deduceInBool(self.instanceExpression).generalize([x], [self.condition])
        # inBool(exists_{x | Q(x)} P(x))
        return inBool(self).check({prerequisite})
    

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

    def remake(self, operator, operands):
        if operator == IMPLIES and len(operands) == 2:
            return Implies(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

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
            return booleans.hypotheticalContraNegation.specialize({A:stmt}).deriveConclusion().check({self, inBool(stmt)})
        else:
            return booleans.hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion().check({self})
    
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

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, [A])
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

    def remake(self, operator, operands):
        if operator == NOT and len(operands) == 1:
            return Not(operands[0])
        else:
            return Operation.remake(self, operator, operands)    
        
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
            return operandEval.lhsSubstitute(Function(Equals(Not(A), val), [A]))
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
        from equality import equality, Equals, x, y
        if isinstance(self.operand, Equals):
            return equality.foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}).deriveConclusion().check({self})
        
class And(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do And(A, B) to get AND{A}{B} or 
        And([A, B, C]) to get AND{A}{AND{B}{C}}, etc.
        '''
        AssociativeBinaryOperation.__init__(self, AND, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'and'
        elif formatType == MATHML:
            return '<mo>&#x2227;</mo>'

    def remake(self, operator, operands):
        if operator == AND:
            return And(operands)
        else:
            return Operation.remake(self, operator, operands)
        
    def deriveLeft(self):
        '''
        From (A and B), derive and return A.
        '''
        return booleans.andImpliesLeft.specialize({A:self.operands[0], B: self.operands[1]}).deriveConclusion().check({self})

    def deriveRight(self):
        '''
        From (A and B), derive and return B.
        '''
        return booleans.andImpliesRight.specialize({A:self.operands[0], B: self.operands[1]}).deriveConclusion().check({self})
        
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
        compose(self.leftOperand, self.rightOperand)
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
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

class Or(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do Or(A, B) to get Or{A}{B} or 
        Or([A, B, C]) to get OR{A}{OR{B}{C}}, etc.
        '''
        AssociativeBinaryOperation.__init__(self, OR, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'or'
        elif formatType == MATHML:
            return '<mo>&#x2228;</mo>'

    def remake(self, operator, operands):
        if operator == OR:
            return Or(operands)
        else:
            return Operation.remake(self, operator, operands)

    def deriveRightIfNotLeft(self):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        return booleans.orImpliesRightIfNotLeft.specialize({A:self.leftOperand, B:self.rightOperand}).deriveConclusion().check({self, Not(self.leftOperand), inBool(self.rightOperand)})

    def deriveLeftIfNotRight(self):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        return booleans.orImpliesLeftIfNotRight.specialize({A:self.leftOperand, B:self.rightOperand}).deriveConclusion().check({self, Not(self.rightOperand), inBool(self.leftOperand)})
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
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

    def remake(self, operator, operands):
        if operator == IFF and len(operands) == 2:
            return Iff(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

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

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE assuming statement.
    '''
    from equality import Equals
    return Equals(statement, TRUE).concludeBooleanEquality()

def compose(exprA, exprB):
    '''
    Returns [exprA and exprB] derived from each separately.
    '''
    return booleans.conjunctionIntro.specialize({A:exprA, B:exprB}).check({exprA, exprB})


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
    return Implies(A, deriveStmtEqTrue(A).concludeBooleanEquality().deriveReversed()).generalize([A]).qed()
booleans.deriveOnDemand('eqTrueRevIntro', eqTrueRevIntroDerivation)

# forall_{A} (TRUE = A) => A
def eqTrueRevElimDerivation():
    from equality import Equals
    hypothesis = Equals(TRUE, A)
    return Implies(hypothesis, hypothesis.deriveReversed().deriveViaBooleanEquality()).generalize([A]).qed()
booleans.deriveOnDemand('eqTrueRevElim', eqTrueRevElimDerivation)

# forall_{A} Not(A) => (FALSE = A)
def notImpliesEqFalseRevDerivation():
    return Implies(Not(A), Not(A).equateNegatedToFalse().deriveReversed()).generalize([A]).qed()
booleans.deriveOnDemand('notImpliesEqFalseRev', notImpliesEqFalseRevDerivation)

# forall_{A} A => TRUE, by a trivial hypothetical reasoning
booleans.deriveOnDemand('trueConclusion', lambda : Implies(A, TRUE).generalize([A]).qed())

# forall_{A} A => A, by a trivial hypothetical reasoning
booleans.deriveOnDemand('selfImplication', lambda : Implies(A, A).generalize([A]).qed())

# (TRUE => TRUE) = TRUE
booleans.deriveOnDemand('impliesTT', lambda : deriveStmtEqTrue(booleans.trueConclusion.specialize({A:TRUE})).qed())

# (FALSE => TRUE) = TRUE
booleans.deriveOnDemand('impliesFT', lambda : deriveStmtEqTrue(booleans.trueConclusion.specialize({A:FALSE})).qed())

# (FALSE => FALSE) = TRUE
booleans.deriveOnDemand('impliesFF', lambda : deriveStmtEqTrue(booleans.selfImplication.specialize({A:FALSE})).qed())

# (TRUE => FALSE) = FALSE
booleans.deriveOnDemand('impliesTF', lambda : booleans.falseImplication.specialize({A:FALSE}).equateNegatedToFalse().qed())

# forall_{A, B} (A <=> B) => (A => B)
booleans.deriveOnDemand('iffImpliesRight', lambda : Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveLeft()).generalize([A, B]).qed())

# forall_{A, B} (A <=> B) => (B => A)
booleans.deriveOnDemand('iffImpliesLeft', lambda : Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveRight()).generalize([A, B]).qed())

# Not(TRUE) => FALSE
booleans.deriveOnDemand('notTimpliesF', lambda : booleans.notT.rightImplViaEquivalence().qed())

# (TRUE <=> TRUE) = TRUE
def iffTTderivation():
    # (TRUE <=> TRUE) = (TRUE => TRUE) and (TRUE => TRUE)
    iffSpecTT = Iff(TRUE, TRUE).definition()
    # [(TRUE => TRUE) and (TRUE => TRUE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = booleans.impliesTT.substitution(Function(And(X, X), [X])).applyTransitivity(booleans.andTT).prove()
    # (TRUE <=> TRUE) = TRUE
    return iffSpecTT.applyTransitivity(rhsEqT).qed()
booleans.deriveOnDemand('iffTT', iffTTderivation)

# (FALSE <=> FALSE) = TRUE
def iffFFderivation():
    # (FALSE <=> FALSE) = (FALSE => FALSE) and (FALSE => FALSE)
    iffSpecFF = Iff(FALSE, FALSE).definition()
    # [(FALSE => FALSE) and (FALSE => FALSE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = booleans.impliesFF.substitution(Function(And(X, X), [X])).applyTransitivity(booleans.andTT).prove()
    # (FALSE <=> FALSE) = TRUE
    return iffSpecFF.applyTransitivity(rhsEqT).qed()
booleans.deriveOnDemand('iffFF', iffFFderivation)

# (TRUE <=> FALSE) = FALSE
def iffTFderivation():
    # (TRUE <=> FALSE) = (TRUE => FALSE) and (FALSE => TRUE)
    iffSpecTF = Iff(TRUE, FALSE).definition()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and (FALSE => TRUE)]
    rhsEqFandFimplT = booleans.impliesTF.substitution(Function(And(X, booleans.impliesFT.lhs), [X])).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and TRUE]
    rhsEqFandT = rhsEqFandFimplT.applyTransitivity(booleans.impliesFT.substitution(Function(And(FALSE, X), [X]))).prove()
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
    rhsEqFimplTandF = booleans.impliesTF.substitution(Function(And(booleans.impliesFT.lhs, X), [X])).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = [TRUE and FALSE]
    rhsEqTandF = rhsEqFimplTandF.applyTransitivity(booleans.impliesFT.substitution(Function(And(X, FALSE), [X]))).prove()
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
    BeqT.lhsSubstitute(Function(And(TRUE, X), [X])).prove({B})
    # (A and B) assuming A, B via (TRUE and TRUE)
    AeqT.lhsSubstitute(Function(And(X, B), [X])).prove({A, B})
    # forall_{A | A, B | B} (A and B)
    return And(A, B).generalize([A, B], [A, B]).qed()
booleans.deriveOnDemand('conjunctionIntro', conjunctionIntroDerivation)

# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
def unfoldInBoolDerivation():
    from sets import sets, In, Singleton
    from equality import Equals
    # [A in ({TRUE} union {FALSE})] assuming inBool(A)
    AinTunionF = booleans.boolsDef.rhsSubstitute(Function(In(A, X), [X])).prove({inBool(A)})
    # (A in {TRUE}) or (A in {FALSE}) assuming inBool(A)
    AinTunionF.unfold().prove({inBool(A)})
    # A=TRUE or (A in {FALSE}) assuming inBool(A)
    sets.singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({inBool(A)})
    # A=TRUE or A=FALSE assuming inBool(A)
    conclusion = sets.singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(Function(Or(Equals(A, TRUE), X), [X])).prove({inBool(A)})
    # forall_{A} inBool(A) => (A=TRUE or A=FALSE)
    return Implies(inBool(A), conclusion).generalize([A]).qed()
booleans.deriveOnDemand('unfoldInBool', unfoldInBoolDerivation)

# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
def foldInBoolDerivation():
    from sets import sets, In, Singleton, Union
    from equality import Equals
    # hypothesis = (A=TRUE or A=FALSE)
    hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
    # (A=TRUE) or (A in {FALSE}) assuming hypothesis
    sets.singletonDef.specialize({x:A, y:FALSE}).lhsSubstitute(Function(Or(Equals(A, TRUE), X), [X])).prove({hypothesis})
    # (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
    sets.singletonDef.specialize({x:A, y:TRUE}).lhsSubstitute(Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({hypothesis})
    # [A in ({TRUE} union {FALSE})] assuming hypothesis
    In(A, Union(Singleton(TRUE), Singleton(FALSE))).concludeAsFolded()
    # (A in BOOLEANS) assuming hypothesis
    booleans.boolsDef.lhsSubstitute(Function(In(A, X), [X])).prove({hypothesis})
    # forall_{A} (A=TRUE or A=FALSE) => inBool(A)
    return Implies(hypothesis, inBool(A)).generalize([A]).qed()
booleans.deriveOnDemand('foldInBool', foldInBoolDerivation)    
    
# forall_{A} Not(A) => [A => FALSE]
def contradictionFromNegationDerivation():
    # FALSE assuming Not(A) and A
    Not(A).equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), A})
    return Implies(Not(A), Implies(A, FALSE)).generalize([A]).qed()
booleans.deriveOnDemand('contradictionFromNegation', contradictionFromNegationDerivation)

# forall_{A} (A=FALSE) => Not(A)
def notFromEqFalseDerivation():
    from equality import Equals
    # AeqF := (A=F)
    AeqF = Equals(A, FALSE)
    # Not(FALSE)
    booleans.notFalse
    # Not(A) assuming A=FALSE because Not(FALSE)
    notA = AeqF.lhsSubstitute(Function(Not(X), [X])).prove({AeqF})
    return Implies(AeqF, notA).generalize([A]).qed()
booleans.deriveOnDemand('notFromEqFalse', notFromEqFalseDerivation)

# forall_{A} (FALSE=A) => Not(A)
def notFromEqFalseRevDerivation():
    from equality import Equals
    # FeqA := (F=A)
    FeqA = Equals(FALSE, A)
    # Not(A) assuming FeqA
    notA = FeqA.deriveReversed().deriveViaBooleanEquality().prove({FeqA})
    return Implies(FeqA, notA).generalize([A]).qed()
booleans.deriveOnDemand('notFromEqFalseRev', notFromEqFalseRevDerivation)

# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
def notOrFromNeitherDerivation():
    # Not(A or B) = Not(F or B) assuming Not(A)
    notAorB_eq_notForB = Not(A).equateNegatedToFalse().substitution(Function(Not(Or(X, B)), [X])).prove({Not(A)})
    # Not(A or B) = Not(F or F) assuming Not(A), Not(B)
    notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(Not(B).equateNegatedToFalse().substitution(Function(Not(Or(FALSE, X)), [X]))).prove({Not(A), Not(B)})
    #  Not(A or B) = Not(F) assuming Not(A), Not(B)
    notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(booleans.orFF.substitution(Function(Not(X), [X]))).prove({Not(A), Not(B)})
    # Not(FALSE)
    booleans.notFalse
    # Not(A or B) assuming Not(A), Not(B)
    notAorB = notAorB_eq_notF.deriveLeftViaEquivalence().prove({Not(A), Not(B)})
    # forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
    return Implies(Not(A), Implies(Not(B), notAorB)).generalize([A, B]).qed()
booleans.deriveOnDemand('notOrFromNeither', notOrFromNeitherDerivation)

# forall_{A, B | Not(A), Not(B)} (A or B) => FALSE
def orContradictionDerivation():
    # (A or B) => FALSE assuming Not(A), Not(B)
    AorB_impl_F = booleans.notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()
    return AorB_impl_F.generalize([A, B], [Not(A), Not(B)]).qed()    
booleans.deriveOnDemand('orContradiction', orContradictionDerivation)

# forall_{A, B | inBool(A), Not(B)} (A or B) => A
def orImpliesLeftIfNotRightDerivation():
    # (A or B) => FALSE assuming Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: A assuming inBool(A), A or B, Not(B)
    Implies(Not(A), FALSE).deriveViaContradiction().prove({inBool(A), Or(A, B), Not(B)})
    # forall_{A, B | inBool(A), Not(B)} (A or B) => A
    return Implies(Or(A, B), A).generalize([A, B], [inBool(A), Not(B)]).qed()
booleans.deriveOnDemand('orImpliesLeftIfNotRight', orImpliesLeftIfNotRightDerivation)

# forall_{A, B | Not(A), inBool(B)} (A or B) => B
def orImpliesRightIfNotLeftDerivation():    
    # (A or B) => FALSE assuming Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: B assuming inBool(B), (A or B), Not(A)
    Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), Or(A, B), Not(A)})
    # forall_{A, B | Not(A), inBool(B)} (A or B) => B
    return Implies(Or(A, B), B).generalize([A, B], [Not(A), inBool(B)]).qed()
booleans.deriveOnDemand('orImpliesRightIfNotLeft', orImpliesRightIfNotLeftDerivation)

# forall_{A} A => Not(Not(A))
def doubleNegationDerivation():
    # A=TRUE assuming A
    AeqT = deriveStmtEqTrue(A)
    # [Not(A)=FALSE] assuming A=TRUE
    AeqT.substitution(Function(Not(X), [X])).applyTransitivity(booleans.notT).prove({AeqT})
    # [Not(A)=FALSE] => Not(Not(A))
    booleans.notFromEqFalse.specialize({A:Not(A)}).prove()
    # forall_{A} A => Not(Not(A))
    return Implies(A, Not(Not(A))).generalize([A]).qed()
booleans.deriveOnDemand('doubleNegation', doubleNegationDerivation)

# forall_{A} A => [Not(A)=FALSE]
def eqFalseFromNegationDerivation():
    # Not(Not(A)) assuming A
    notNotA = Not(Not(A)).concludeViaDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse()).generalize([A]).qed()
booleans.deriveOnDemand('eqFalseFromNegation', eqFalseFromNegationDerivation)

# forall_{A} A => [FALSE=Not(A)]
def eqFalseRevFromNegationDerivation():
    # Not(Not(A)) assuming A
    notNotA = Not(Not(A)).concludeViaDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse().deriveReversed()).generalize([A]).qed()
booleans.deriveOnDemand('eqFalseRevFromNegation', eqFalseRevFromNegationDerivation)

# forall_{A | inBool(A)} Not(Not(A)) => A
def fromDoubleNegationDerivation():
    # hypothesis = Not(Not(A))
    hypothesis = Not(Not(A)).state()
    # FALSE assuming Not(A), Not(Not(A))
    hypothesis.equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), hypothesis})
    # [Not(A) => FALSE] => A assuming inBool(A)
    booleans.hypotheticalContraNegation.specialize().prove({inBool(A)})
    # inBool(A) => [Not(Not(A)) => A] via hypothetical reasoning
    return Implies(hypothesis, A).generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('fromDoubleNegation', fromDoubleNegationDerivation)

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
    return Implies(AnotF, A).generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('fromNotFalse', fromNotFalseDerivation)

# forall_{A, B | inBool(B)} [Not(B) => Not(A)] => [A=>B] 
def transpositionFromNegatedDerivation():
    # Contradiction proof of B assuming (Not(B)=>Not(A)), A, and inBool(B)
    notBimplNotA = Implies(Not(B), Not(A)).state()
    # A=FALSE assuming Not(B)=>Not(A) and Not(B)
    AeqF = notBimplNotA.deriveConclusion().equateNegatedToFalse().prove({notBimplNotA, Not(B)})
    # FALSE assuming Not(B)=>Not(A), Not(B), and A
    AeqF.deriveRightViaEquivalence().prove({notBimplNotA, Not(B), A})
    # B assuming inBool(B), (Not(B)=>Not(A)), A
    Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), notBimplNotA, A})
    # [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming inBool(B)
    transpositionExpr = Implies(notBimplNotA, Implies(A, B)).prove({inBool(B)})
    # forall_{A, B | inBool(B)} [A => B] => [Not(B) => Not(A)]
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
booleans.deriveOnDemand('transpositionFromNegated', transpositionFromNegatedDerivation)

# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
def doubleNegateConclusionDerivation():
    # Not(Not(B)) assuming B and inBool(B)
    notNotB = Not(Not(B)).concludeViaDoubleNegation()
    # [A=>B] => [A => Not(Not(B))] assuming inBool(B)
    innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
    # forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
    return innerExpr.generalize([A, B], [inBool(B)]).qed()
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
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('transpositionFromNegatedHypothesis', transpositionFromNegatedHypothesisDerivation)

# forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
def transpositionFromNegatedConclusionDerivation():
    from equality import Equals, NotEquals
    # inBool(B=FALSE)
    Equals(B, FALSE).deduceInBool()
    # [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using inBool(B=FALSE)
    midPointBackHalf = Implies(Not(Equals(B, FALSE)), Not(A)).transposition()
    # [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
    midPointFrontHalf = NotEquals(B, FALSE).definition().rhsStatementSubstitution(Function(Implies(X, Not(A)), [X])).prove()
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
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
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
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
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
    AnotF = AeqT.lhsSubstitute(Function(NotEquals(X, FALSE), [X])).prove({A})
    # forall_{A} A => (A != FALSE)
    return Implies(A, AnotF).generalize([A]).qed()
booleans.deriveOnDemand('notEqualsFalse', notEqualsFalseDerivation)

# inBool(TRUE)
def trueInBoolDerivation():
    from equality import Equals
    # [TRUE or FALSE] 
    booleans.orTF.deriveViaBooleanEquality().prove()
    # [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
    booleans.trueNotFalse.unfold().equateNegatedToFalse().lhsSubstitute(Function(Or(TRUE, X), [X])).prove()
    # [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
    deriveStmtEqTrue(booleans.trueEqTrue).lhsSubstitute(Function(Or(X, Equals(TRUE, FALSE)), [X])).prove()
    # inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
    return inBool(TRUE).concludeAsFolded().qed()
booleans.deriveOnDemand('trueInBool', trueInBoolDerivation)

# inBool(FALSE)
def falseInBoolDerivation():
    from equality import Equals
    # [FALSE or TRUE] 
    booleans.orFT.deriveViaBooleanEquality().prove()
    # [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
    deriveStmtEqTrue(booleans.falseEqFalse).lhsSubstitute(Function(Or(FALSE, X), [X])).prove()
    # [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
    booleans.falseNotTrue.unfold().equateNegatedToFalse().lhsSubstitute(Function(Or(X, Equals(FALSE, FALSE)), [X])).prove()
    # inBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
    return inBool(FALSE).concludeAsFolded().qed()
booleans.deriveOnDemand('falseInBool', falseInBoolDerivation)

# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
def unfoldForallOverBoolDerivation():
    # hypothesis = [forall_{A in BOOLEANS} P(A)]
    hypothesis = Forall([A], PofA, [inBool(A)])
    # TRUE in BOOLEANS, FALSE in BOOLEANS
    booleans.trueInBool, booleans.falseInBool
    # P(TRUE) and P(FALSE) assuming hypothesis
    conclusion = compose(hypothesis.specialize({A:TRUE}), hypothesis.specialize({A:FALSE})).prove({hypothesis})
    # forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
    return Implies(hypothesis, conclusion).generalize([P]).qed()
booleans.deriveOnDemand('unfoldForallOverBool', unfoldForallOverBoolDerivation)

# forall_{A} A=TRUE => inBool(A)
def inBoolIfEqTrueDerivation():
    from equality import Equals
    # hypothesis = (A=TRUE)
    hypothesis = Equals(A, TRUE)
    # inBool(TRUE)
    booleans.trueInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.lhsSubstitute(Function(inBool(X), [X])).prove({hypothesis})
    # forall_{A} A=TRUE => inBool(A)
    return Implies(hypothesis, conclusion).generalize([A]).qed()
booleans.deriveOnDemand('inBoolIfEqTrue', inBoolIfEqTrueDerivation)

# forall_{A} TRUE=A => inBool(A)
def inBoolIfEqTrueRevDerivation():
    from equality import Equals
    # hypothesis = (TRUE=A)
    hypothesis = Equals(TRUE, A)
    # inBool(TRUE)
    booleans.trueInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.rhsSubstitute(Function(inBool(X), [X])).prove({hypothesis})
    # forall_{A} (TRUE=A) => inBool(A)
    return Implies(hypothesis, conclusion).generalize([A]).qed()
booleans.deriveOnDemand('inBoolIfEqTrueRev', inBoolIfEqTrueRevDerivation)

# forall_{A} A=FALSE => inBool(A)
def inBoolIfEqFalseDerivation():
    from equality import Equals
    # hypothesis = (A=FALSE)
    hypothesis = Equals(A, FALSE)
    # inBool(FALSE)
    booleans.falseInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.lhsSubstitute(Function(inBool(X), [X])).prove({hypothesis})
    # forall_{A} A=FALSE => inBool(A)
    return Implies(hypothesis, conclusion).generalize([A]).qed()
booleans.deriveOnDemand('inBoolIfEqFalse', inBoolIfEqFalseDerivation)

# forall_{A} FALSE=A => inBool(A)
def inBoolIfEqFalseRevDerivation():
    from equality import Equals
    # hypothesis = (FALSE=A)
    hypothesis = Equals(FALSE, A)
    # inBool(FALSE)
    booleans.falseInBool.prove()
    # inBool(A) assuming hypothesis
    conclusion = hypothesis.rhsSubstitute(Function(inBool(X), [X])).prove({hypothesis})
    # forall_{A} (FALSE=A) => inBool(A)
    return Implies(hypothesis, conclusion).generalize([A]).qed()
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
    deriveStmtEqTrue(C).rhsSubstitute(Function(Not(X), [X])).prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # FALSE assuming inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    booleans.notT.deriveRightViaEquivalence().prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # Contradiction proof of C assuming (A=>C and B=>C), (A or B), inBool(A), and inBool(B)
    Implies(Not(C), FALSE).deriveViaContradiction().prove(ABCareBool | {hypothesis, AorB})
    return Implies(hypothesis, Implies(AorB, C)).generalize([A, B, C], ABCareBoolInOrder).qed()
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
    # [A=TRUE => P(A)=TRUE and A=FALSE => P(A)=TRUE] => [(A=TRUE or A=FALSE) => P(A)=TRUE]
    specDisj = booleans.hypotheticalDisjunction.specialize({A:AeqT, B:AeqF, C:PofAeqT}).prove()
    # A=TRUE => P(A)=TRUE assuming hypothesis
    AeqTimplPofA = Implies(AeqT, deriveStmtEqTrue(AeqT.lhsSubstitute(Function(PofA, [A])))).prove({hypothesis})
    # A=FALSE => P(A)=TRUE assuming hypothesis
    AeqFimplPofA = Implies(AeqF, deriveStmtEqTrue(AeqF.lhsSubstitute(Function(PofA, [A])))).prove({hypothesis})
    # [A=TRUE => P(A) and A=FALSE => P(A)=TRUE] assuming hypothesis
    compose(AeqTimplPofA, AeqFimplPofA).prove({hypothesis})
    # [(A=TRUE or A=FALSE) => P(A)=TRUE] assuming hypothesis
    AeqTorAeqFimplPofAeqT = specDisj.deriveConclusion().prove({hypothesis})
    # (A=TRUE or A=FALSE) => P(A)
    Implies(AeqTorAeqFimplPofAeqT.hypothesis, AeqTorAeqFimplPofAeqT.deriveConclusion().deriveViaBooleanEquality()).prove({hypothesis})
    # forall_{A in BOOLEANS} P(A) assuming hypothesis
    conclusion = PofA.generalize([A], [inBool(A).concludeAsFolded()]).prove({hypothesis})
    # forall_{P} P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
    return Implies(hypothesis, conclusion).generalize([P]).qed()
booleans.deriveOnDemand('foldForallOverBool', foldForallOverBoolDerivation)

# forall_{P} [P(TRUE) and P(FALSE)] => {forall_{A in BOOLEANS} P(A) = TRUE}
def forallBoolEvalTrueDerivation():
    # P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
    folding = booleans.foldForallOverBool.specialize()
    # forall_{P} [P(TRUE) and P(FALSE)] => {forall_{A in BOOLEANS} P(A) = TRUE}
    return Implies(folding.hypothesis, deriveStmtEqTrue(folding.deriveConclusion())).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalTrue', forallBoolEvalTrueDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
def iffOverBoolImplEqDerivation():
    from equality import Equals
    return Forall([A, B], Implies(Iff(A, B), Equals(A, B)), [inBool(A), inBool(B)]).proveByEval()
booleans.deriveOnDemand('iffOverBoolImplEq', iffOverBoolImplEqDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A => B) in BOOLEANS                                                                                                        
def implicationClosureDerivation():
    from equality import Equals
    # [(A=>B) = TRUE] or [(A=>B) = FALSE] assuming A, B in BOOLEANS
    Forall([A, B], Or(Equals(Implies(A, B), TRUE), Equals(Implies(A, B), FALSE)), [inBool(A), inBool(B)]).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A => B) in BOOLEANS  
    return inBool(Implies(A, B)).concludeAsFolded().generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('implicationClosure', implicationClosureDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) in BOOLEANS                                                                                                        
def iffClosureDerivation():
    from equality import Equals
    # [(A<=>B) = TRUE] or [(A<=>B) = FALSE] assuming A, B in BOOLEANS
    Forall([A, B], Or(Equals(Iff(A, B), TRUE), Equals(Iff(A, B), FALSE)), [inBool(A), inBool(B)]).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A <=> B) in BOOLEANS  
    return inBool(Iff(A, B)).concludeAsFolded().generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('implicationClosure', implicationClosureDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A and B) in BOOLEANS                                                                                                        
def conjunctionClosureDerivation():
    from equality import Equals
    # [(A and B) = TRUE] or [(A and B) = FALSE] assuming A, B in BOOLEANS
    Forall([A, B], Or(Equals(And(A, B), TRUE), Equals(And(A, B), FALSE)), [inBool(A), inBool(B)]).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A and  B) in BOOLEANS  
    return inBool(And(A, B)).concludeAsFolded().generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('conjunctionClosure', conjunctionClosureDerivation)

# forall_{A in BOOLEANS, B in BOOLEANS} (A of B) in BOOLEANS                                                                                                        
def disjunctionClosureDerivation():
    from equality import Equals
    # [(A or B) = TRUE] or [(A or B) = FALSE] assuming A, B in BOOLEANS
    Forall([A, B], Or(Equals(Or(A, B), TRUE), Equals(Or(A, B), FALSE)), [inBool(A), inBool(B)]).proveByEval().specialize().prove({inBool(A), inBool(B)})
    # forall_{A in BOOLEANS} (A or  B) in BOOLEANS  
    return inBool(Or(A, B)).concludeAsFolded().generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('disjunctionClosure', disjunctionClosureDerivation)

# forall_{A in BOOLEANS} Not(A) in BOOLEANS                                                                                                        
def negationClosureDerivation():
    from equality import Equals
    # Not(A) = TRUE or Not(A) = FALSE assuming A in BOOLEANS
    Forall([A], Or(Equals(Not(A), TRUE), Equals(Not(A), FALSE)), [inBool(A)]).proveByEval().specialize().prove({inBool(A)})
    # forall_{A in BOOLEANS} Not(A) in BOOLEANS  
    return inBool(Not(A)).concludeAsFolded().generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('negationClosure', negationClosureDerivation)

# forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                            
def hypotheticalContradictionDerivation():
    # inBool(Not(A)) assuming inBool(A)    
    Not(A).deduceInBool().prove({inBool(A)})
    # [Not(Not(A)) => FALSE] => Not(A) assuming inBool(A)                                     
    booleans.hypotheticalContraNegation.specialize({A:Not(A)}).prove({inBool(A)})
    # A assuming Not(Not(A)) and inBool(A)                                                    
    Not(Not(A)).deriveViaDoubleNegation().prove({inBool(A), Not(Not(A))})
    # forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                        
    return Implies(Implies(A, FALSE), Not(A)).generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('hypotheticalContradiction', hypotheticalContradictionDerivation)

# forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
def existenceByExampleDerivation():
    from equality import NotEquals
    # PyNeverTrue = (forall_{y | Q(y)} P(y) != TRUE)
    PyNeverTrue = Forall([y], NotEquals(Py, TRUE), [Qy])
    # P(x) != TRUE assuming Q(x), PyNeverTrue
    PyNeverTrue.specialize({y:x}).prove({Qx, PyNeverTrue})
    # Not(TRUE = TRUE) assuming Q(x), P(x), PyNeverTrue
    notTeqT = deriveStmtEqTrue(Px).rhsSubstitute(Function(NotEquals(X, TRUE), [X])).unfold().prove({Qx, Px, PyNeverTrue})
    # FALSE assuming Q(x), P(x), PyNeverTrue
    notTeqT.evaluate().deriveRightViaEquivalence().prove({Qx, Px, PyNeverTrue})
    # inBool(forall_{y | Q(y)} P(y) != TRUE)
    PyNeverTrue.deduceInBool().prove()
    # Not(forall_{y | Q(y)} P(y) != TRUE) assuming Q(x), P(x)
    Implies(PyNeverTrue, FALSE).deriveViaContradiction().prove({Qx, Px})
    # exists_{y | Q(y)} P(y) assuming Q(x), P(x)
    existence = booleans.existsDef.specialize({x:y}).deriveLeft().prove({Qx, Px})
    # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(y)} P(y)]
    return Implies(Px, existence).generalize([P, Q, x], [Qx]).qed()
booleans.deriveOnDemand('existenceByExample', existenceByExampleDerivation)

# forall_{P, Q} forall_{x | Q(x)} [P(x) in BOOLEANS] => [exists_{x | Q(x)} P(x) <=> Not(forall_{x | Q(x)} Not(P(x))]
def existenceOverBoolStmtsDerivation():
    from equality import Equals, NotEquals
    # hypothesis = forall_{x | Q(x)} [P(x) in BOOLEANS]
    hypothesis = Forall([x], inBool(Px), [Qx])
    # P(x) in BOOLEANS assuming hypothesis, Q(x)
    hypothesis.specialize().prove({hypothesis, Qx})
    # forall_{x | Q(x)} {[P(x) != TRUE] = Not(P(x))} assuming hypothesis
    PxNotT_eq_NotPx = Forall([A], Equals(NotEquals(A, TRUE), Not(A)), [inBool(A)]).evaluate().deriveViaBooleanEquality().specialize({A:Px}).generalize([x], [Qx]).prove({hypothesis})
    # [forall_{x | Q(x)} (P(x) != TRUE)] = [forall_{x | Q(x)} Not(P(x))] assuming hypothesis
    PxNeverT_eq_AlwaysNotPx = PxNotT_eq_NotPx.instanceSubstitution(FORALL).prove({hypothesis})
    # exists_{x | Q(x)} P(x) <=> Not[forall_{x | Q(x)} (P(x) != TRUE)]
    existsDefSpec = booleans.existsDef.specialize().prove()
    # exists_{x | Q(x)} P(x) <=> Not[forall_{x | Q(x)} Not(P(x))] assuming hypothesis    
    conclusion = PxNeverT_eq_AlwaysNotPx.rhsSubstitute(Function(Iff(existsDefSpec.A, Not(X)), [X])).prove({hypothesis})
    # forall_{P, Q} forall_{x | Q(x)} [P(x) in BOOLEANS] => [exists_{x | Q(x)} P(x) <=> Not(forall_{x | Q(x)} Not(P(x))]
    return Implies(hypothesis, conclusion).generalize([P, Q]).qed()
booleans.deriveOnDemand('existenceOverBoolStmts', existenceOverBoolStmtsDerivation)

# forall_{P, Q} forall_{x | Q(x)} [P(x) in BOOLEANS] => [exists_{x | Q(x)} Not(P(x)) <=> Not(forall_{x | Q(x)} P(x)]
def existenceOverNegatedDerivation():
    from equality import Equals, NotEquals
    # hypothesis = forall_{x | Q(x)} [P(x) in BOOLEANS]
    hypothesis = Forall([x], inBool(Px), [Qx])
    # P(x) in BOOLEANS assuming hypothesis, Q(x)
    hypothesis.specialize().prove({hypothesis, Qx})
    # forall_{x | Q(x)} [Not(P(x)) != TRUE] = P(x) assuming hypothesis
    NotPxNotT_eq_Px = Forall([A], Equals(NotEquals(Not(A), TRUE), A), [inBool(A)]).evaluate().deriveViaBooleanEquality().specialize({A:Px}).generalize([x], [Qx]).prove({hypothesis})
    # [forall_{x | Q(x)} Not(P(x)) != TRUE] = [forall_{x | Q(x)} P(x)] assuming hypothesis
    NotPxNeverT_eq_AlwaysPx = NotPxNotT_eq_Px.instanceSubstitution(FORALL).prove({hypothesis})
    # exists_{x | Q(x)} Not(P(x)) <=> Not[forall_{x | Q(x)} (Not(P(x)) != TRUE)]
    existsDefSpec = booleans.existsDef.specialize({P:Function(Not(Px), [x])}).prove()
    # exists_{x | Q(x)} Not(P(x)) <=> Not[forall_{x | Q(x)} P(x)] assuming hypothesis    
    conclusion = NotPxNeverT_eq_AlwaysPx.rhsSubstitute(Function(Iff(existsDefSpec.A, Not(X)), [X])).prove({hypothesis})
    # forall_{P, Q} forall_{x | Q(x)} [P(x) in BOOLEANS] => [exists_{x | Q(x)} P(x) <=> Not(forall_{x | Q(x)} Not(P(x))]
    return Implies(hypothesis, conclusion).generalize([P, Q]).qed()
booleans.deriveOnDemand('existenceOverNegated', existenceOverNegatedDerivation)

# forall_{P} [(P(TRUE) = FALSE) and (P(FALSE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
def forallBoolEvalFalseViaTrueDerivation():
    from equality import Equals
    # hypothesis = [P(TRUE) = FALSE] and (P(FALSE) in BOOLEANS)
    hypothesis = And(Equals(PofTrue, FALSE), inBool(PofFalse))
    # P(TRUE) in BOOLEANS assuming hypothesis
    hypothesis.deriveLeft().inBoolViaBooleanEquality().prove({hypothesis})
    # P(FALSE) in BOOLEANS assuming hypothesis
    hypothesis.deriveRight().prove({hypothesis})
    # forall_{A in BOOLEANS} P(A) in BOOLEANS assuming hypothesis
    Forall([A], inBool(PofA), [inBool(A)]).concludeAsFolded().prove({hypothesis})
    # Not(P(TRUE) assuming hypothesis
    hypothesis.deriveLeft().deriveViaBooleanEquality().prove({hypothesis})
    # [forall_{A in BOOLEANS} P(A) = FALSE] assuming hypothesis
    conclusion = Exists([A], Not(PofA), [inBool(A)]).concludeViaExample(TRUE).unfold().equateNegatedToFalse().prove({hypothesis})
    # forall_{P} [(P(TRUE) = FALSE) and (P(FALSE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, conclusion).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalFalseViaTrue', forallBoolEvalFalseViaTrueDerivation)

# forall_{P} [(P(FALSE) = FALSE) and (P(TRUE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
def forallBoolEvalFalseViaFalseDerivation():
    from equality import Equals
    # hypothesis = [(P(FALSE) = FALSE) and (P(TRUE) in BOOLEANS)]
    hypothesis = And(Equals(PofFalse, FALSE), inBool(PofTrue))
    # P(FALSE) in BOOLEANS assuming hypothesis
    hypothesis.deriveLeft().inBoolViaBooleanEquality().prove({hypothesis})
    # P(TRUE) in BOOLEANS assuming hypothesis
    hypothesis.deriveRight().prove({hypothesis})
    # forall_{A in BOOLEANS} P(A) in BOOLEANS assuming hypothesis
    Forall([A], inBool(PofA), [inBool(A)]).concludeAsFolded().prove({hypothesis})
    # Not(P(FALSE) assuming hypothesis
    hypothesis.deriveLeft().deriveViaBooleanEquality().prove({hypothesis})
    # [forall_{A in BOOLEANS} P(A) = FALSE] assuming hypothesis
    conclusion = Exists([A], Not(PofA), [inBool(A)]).concludeViaExample(FALSE).unfold().equateNegatedToFalse().prove({hypothesis})
    # forall_{P} [(P(FALSE) = FALSE) and (P(TRUE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, conclusion).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalFalseViaFalse', forallBoolEvalFalseViaFalseDerivation)
