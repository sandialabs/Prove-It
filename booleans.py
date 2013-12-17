from proveItCore import *
from genericOperations import *

class BooleanContext(Context):
    def __init__(self):
        Context.__init__(self, 'BOOLEANS')
        self.eval = [] # list of registered evaluations
    
    def registerEvaluation(self, evaluation):
        if evaluation != None:
            if evaluation.qed().statement.getRegisteredVar() == None:
                booleans.eval.append(evaluation)
                booleans.register('eval', len(booleans.eval)-1)

    def evaluateBooleanBinaryOperation(self, operation, baseEvalFn):
        from equality import equality, f, a, b, c, x, y
        prevContext = Context.current
        Context.current = booleans
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
        Context.current = prevContext
        self.registerEvaluation(evaluation)
        return evaluation    
    
booleans = BooleanContext()

# boolean related literals
IMPLIES = booleans.addLiteral('IMPLIES')
IFF = booleans.addLiteral('IFF')
TRUE = booleans.addLiteral('TRUE', {MATHML:'<mstyle mathvariant="normal"><mi>true</mi></mstyle>'})
FALSE = booleans.addLiteral('FALSE', {MATHML:'<mstyle mathvariant="normal"><mi>false</mi></mstyle>'})
NOT = booleans.addLiteral('NOT')
AND = booleans.addLiteral('AND')
OR = booleans.addLiteral('OR')
BOOLEANS = booleans.addLiteral('BOOLEANS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x1D539;</mtext><mspace/></mstyle>'})
FORALL = booleans.addLiteral('FORALL')
EXISTS = booleans.addLiteral('EXISTS')

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
PofTrue = Operation(P, [TRUE])
PofFalse = Operation(P, [FALSE])
PofA = Operation(P, [A])
X = Variable('X')

def booleanAxioms():
    """
    Generates the boolean axioms.  Because of the interdependence of booleans, 
    equality, and sets, this is executed on demand after these have all loaded.
    """
    
    from sets import Union, Singleton
    from equality import Equals, NotEquals
    importVars = set(locals().keys()) | {'importVars'}

    # BOOLEANS = {TRUE} union {FALSE}
    boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))

    # forall_{P, x} {Q(x) and Not(P(x)) => Not(forall_{y | Q(y)} P(y))}
    forallNegation = Forall([P, Q, x], Implies(And(Qx, Not(Px)), Not(Forall([y], Py, [Qy]))))

    # forall_{P, x} [P(x) => exists_{y} P(y)]
    existsDef = Forall([P, x], Implies(Px, Exists([y], Py)))    
    
    # forall_{P, Q} {exists_{x | Q(x)} P(x) <=> exists_{x} [P(x) and Q(x)]}
    existsSuchThatDef = Forall([P, Q], Iff(Exists([x], Px, [Qx]), Exists([x], And(Px, Qx))))
    
    # FALSE != TRUE
    falseNotTrue = NotEquals(FALSE, TRUE)
        
    # TRUE is a true statement
    trueAxiom = TRUE
        
    # Truth table for NOT
    notF = Equals(Not(FALSE), TRUE)
    notT = Equals(Not(TRUE), FALSE)
    
    # Further defining property of NOT needed in addition to the truth table
    # because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.
    
    # forall_{A} not(A) => [A=FALSE]
    notImpliesEqFalse = Forall([A], Implies(Not(A), Equals(A, FALSE)))
    
    # Truth table for AND
    andTT = Equals(And(TRUE, TRUE), TRUE)
    andTF = Equals(And(TRUE, FALSE), FALSE)
    andFT = Equals(And(FALSE, TRUE), FALSE)
    andFF = Equals(And(FALSE, FALSE), FALSE)
    
    # Further defining properties of AND needed in addition to the truth table
    # because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE.
    
    # forall_{A, B} A and B => A
    andImpliesLeft = Forall([A, B], Implies(And(A, B), A))
    # forall_{A, B} A and B => B
    andImpliesRight = Forall([A, B], Implies(And(A, B), B))
    
    
    # Truth table for OR
    orTT = Equals(Or(TRUE, TRUE), TRUE)
    orTF = Equals(Or(TRUE, FALSE), TRUE)
    orFT = Equals(Or(FALSE, TRUE), TRUE)
    orFF = Equals(Or(FALSE, FALSE), FALSE)
    
    # forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
    iffDef = Forall([A, B], Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))
    
    # forall_{A} A => (A = TRUE)
    eqTrueIntro = Forall([A], Implies(A, Equals(A, TRUE)))
    # forall_{A} (A = TRUE) => A
    eqTrueElim = Forall([A], Implies(Equals(A, TRUE), A))
    
    # forall_{A | Not(A=T)} Not(TRUE => A)
    falseImplication = Forall([A], Not(Implies(TRUE, A)), [NotEquals(A, TRUE)])
    
    # forall_{A | inBool(A)} [Not(A) => FALSE] => A
    hypotheticalContraNegation = Forall([A], Implies(Implies(Not(A), FALSE), A), [inBool(A)])
    # Note that implies has a deriveContradiction method that applies this axiom.
    
    allLocals = dict(locals())
    return {key:allLocals[key] for key in (set(allLocals.keys()) - importVars)}
    
booleans.axiomsOnDemand(booleanAxioms)

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
        #  [(element = TRUE) or (element = FALSE)] given inBool(element)
        return booleans.unfoldInBool.specialize({A:element}).deriveConclusion().check({inBool(element)})
    
    def proveElemInSet(self, element):
        '''
        From [(element = TRUE) or (element = FALSE)], derive and return [element in BOOLEANS].
        '''   
        from equality import Equals
        # prerequisite = [(element = TRUE) or (element = FALSE)]
        prerequisite = Or(Equals(element, TRUE), Equals(element, FALSE))
        # [element in BOOLEANS] given prerequisite
        return booleans.foldInBool.specialize({A:element}).deriveConclusion().check({prerequisite})

    def evaluateForallInSet(self, forallStmt):
        '''
        Given a forall statement over the set of Booleans, evaluate to TRUE or FALSE
        if possible.
        '''
        # THIS IS THE IMPLEMENTATION FOR THE BOOLEAN DOMAIN: TODO, SOMETHING LIKE IN In.unfold(..) WHERE
        # IT CALLS THE METHOD OF THE APPROPRIATE CLASS AND CAN BE GENERALIZED
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
                    compose(evalTrueInstance.deriveFromBooleanEquality(), evalFalseInstance.deriveFromBooleanEquality())
                    evaluation = booleans.forallBoolEvalTrue.specialize({P:instanceFn}).deriveConclusion()
        booleans.registerEvaluation(evaluation)
        return evaluation

BOOLEANS = booleans.addLiteral(literal = BooleanSet())

    
class Forall(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Nest Forall OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, FORALL, lambda iVars, iExpr, conds: Forall(iVars, iExpr, conds), instanceVars, instanceExpression, conditions)

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
        return self.condition != None and isinstance(self.condition, In) and self.condition.element == self.instanceVar

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == FORALL:
            return Forall([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)

    def evaluate(self):
        '''
        Given a forall statement with some condition, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        return self.condition.evaluateForall(self)

class Exists(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Nest Exists OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.  For convenience, conditions of the form 
        In(instanceVar, domain) may be provided implicitly via tuples in the instanceVars collection.  
        For example, instanceVars=[(a, A), (b, B)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, A), In(b, B)].  You can also provide multiple instance variables per domain 
        as in the following: instanceVars=[([a, b], S)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, S), In(b, S)].  These implicit conditions are prepended to any explicitly 
        given conditions as this is processed.
        '''
        NestableOperationOverInstances.__init__(self, EXISTS, lambda iVars, iExpr, conds: Exists(iVars, iExpr, conds), instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'exist'
        elif formatType == MATHML:
            return '<mo>&#x2203;</mo>'

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == EXISTS:
            return Exists([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)  

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
        From (A=>B) derive and return B given A.
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
    
    def deriveHypotheticalContradiction(self):
        '''
        From [Not(A)=>FALSE], derive and return A given inBool(A).
        Or from (A=>FALSE), derive and return Not(A).
        '''
        assert self.conclusion == FALSE
        if isinstance(self.hypothesis, Not):
            stmt = self.hypothesis.operand
            return booleans.hypotheticalContraNegation.specialize({A:stmt}).deriveConclusion().check({self, inBool(stmt)})
        else:
            return booleans.hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion().check({self})
    
    def generalize(self, newForallVars, newConditions=None):
        '''
        This makes a generalization of this expression, prepending Forall 
        operations according to newForallVars and newConditions that will bind
        'arbitrary' free variables.  This overrides the Expression version
        to absorb hypothesis into conditions if they match.  For example, 
        [A(x) => [B(x, y) => P(x, y)]] generalized forall_{x, y | A(x), B(x, y)}
        becomes forall_{x | A(x)} forall_{y | B(x, y)} P(x, y),
        '''
        hypothesizedConditions = set()
        newConditionsSet = set(newConditions) if newConditions != None else set()
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
        will as follows:
        For [Not(A) => Not(B)], derive [Not(A) => Not(B)] => [B => A] given inBool(A).
        For [Not(A) => B], derive [Not(A) => B] => [Not(B) => A] given inBool(A), inBool(B).
        For [A => Not(B)], derive [A => Not(B)] => [B => Not(A)] given inBool(A).
        For [A => B], derive [A => B] => [Not(B) => Not(A)] given inBool(A), inBool(B)
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
        From Not(A) => Not(B), derive and return B => A given inBool(A).
        From Not(A) => B, derive Not(B) => A given inBool(A), inBool(B).
        From A => Not(B), derive B => Not(A) given inBool(A).
        From A => B, derive Not(B) => Not(A).
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
        return booleans.evaluateBooleanBinaryOperation(self, baseEvalFn)    

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
        if self.operand == TRUE: return booleans.notT
        elif self.operand == FALSE: return booleans.notF
        operandEval = self.operand.evaluate()
        evaluation = operandEval.rhsSubstitute(Function(Not(A), [A])).evaluate()
        booleans.registerEvaluation(evaluation)
        return evaluation
    
    def equateNegatedToFalse(self):
        '''
        From Not(A), derive and return [A = FALSE].
        Note, see Equals.deriveFromBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalse.specialize({A:self.operand}).deriveConclusion().check({self})

    def equateFalseToNegated(self):
        '''
        From Not(A), derive and return [FALSE = A].
        Note, see Equals.deriveFromBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalseRev.specialize({A:self.operand}).deriveConclusion().check({self})
    
    def deriveFromDoubleNegation(self):
        '''
        From Not(Not(A)), return A given inBool(A).
        Also see version in NotEquals for A != FALSE.
        '''
        if isinstance(self.operand, Not):
            return booleans.fromDoubleNegation.specialize({A:self.operand.operand}).deriveConclusion().check({self, inBool(A)})

    def proveByDoubleNegation(self):
        '''
        Prove and return self of the form Not(Not(A)) given A.
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

    def proveByComposition(self):
        '''
        Prove and return some (A and B) given A, B.  See also the compose method to
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
        return booleans.evaluateBooleanBinaryOperation(self, baseEvalFn)

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
        From (A or B) derive and return B given Not(A), inBool(B). 
        '''
        return booleans.orImpliesRightIfNotLeft.specialize({A:self.leftOperand, B:self.rightOperand}).deriveConclusion().check({self, Not(self.leftOperand), inBool(self.rightOperand)})

    def deriveLeftIfNotRight(self):
        '''
        From (A or B) derive and return A given inBool(A), Not(B).
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
        return booleans.evaluateBooleanBinaryOperation(self, baseEvalFn)

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
        From (A<=>B) derive and return A given B.
        '''
        return self.deriveLeftImplication().deriveConclusion().check({self, self.B})

    def deriveRightImplication(self):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        return booleans.iffImpliesRight.specialize({A: self.A, B: self.B}).deriveConclusion().check({self})

    def deriveRight(self):
        '''
        From (A<=>B) derive and return B given A.
        '''
        return self.deriveRightImplication().deriveConclusion().check({self, self.A})
    
    def definition(self):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        return booleans.iffDef.specialize({A:self.A, B:self.B}).check()
    
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
        return booleans.evaluateBooleanBinaryOperation(self, baseEvalFn)      

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE given statement.
    '''
    from equality import Equals
    return Equals(statement, TRUE).proveByBooleanEquality()

def compose(exprA, exprB):
    '''
    Returns [exprA and exprB] derived from each separately.
    '''
    return booleans.conjunctionIntro.specialize({A:exprA, B:exprB}).check({exprA, exprB})


# DERIVATIONS

# Not(FALSE)
booleans.deriveOnDemand('notFalse', lambda : booleans.notF.deriveFromBooleanEquality().qed())
    
# TRUE and TRUE
booleans.deriveOnDemand('trueAndTrue', lambda : booleans.andTT.deriveFromBooleanEquality().qed())
    
# TRUE or TRUE
booleans.deriveOnDemand('trueOrTrue', lambda : booleans.orTT.deriveFromBooleanEquality().qed())
    
# TRUE or FALSE
booleans.deriveOnDemand('trueOrFalse', lambda : booleans.orTF.deriveFromBooleanEquality().qed())
    
# FALSE or TRUE
booleans.deriveOnDemand('falseOrTrue', lambda : booleans.orFT.deriveFromBooleanEquality().qed())

# TRUE = TRUE
def trueEqTrueDerivation():
    from equality import Equals
    return Equals(TRUE, TRUE).proveByReflexivity().qed()
booleans.deriveOnDemand('trueEqTrue', trueEqTrueDerivation)

# FALSE = FALSE
def falseEqFalseDerivation():
    from equality import Equals
    return Equals(FALSE, FALSE).proveByReflexivity().qed()
booleans.deriveOnDemand('falseEqFalse', falseEqFalseDerivation)

# forall_{A} A => (TRUE = A)
def eqTrueRevIntroDerivation():
    return Implies(A, deriveStmtEqTrue(A).proveByBooleanEquality().deriveReversed()).generalize([A]).qed()
booleans.deriveOnDemand('eqTrueRevIntro', eqTrueRevIntroDerivation)

# forall_{A} (TRUE = A) => A
def eqTrueRevElimDerivation():
    from equality import Equals
    hypothesis = Equals(TRUE, A)
    return Implies(hypothesis, hypothesis.deriveReversed().deriveFromBooleanEquality()).generalize([A]).qed()
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
    # A=TRUE given A
    AeqT = deriveStmtEqTrue(A).prove({A})
    # B=TRUE given B
    BeqT = deriveStmtEqTrue(B).prove({B})
    # TRUE AND TRUE
    booleans.trueAndTrue
    # (TRUE and B) given B via (TRUE and TRUE)
    BeqT.lhsSubstitute(Function(And(TRUE, X), [X])).prove({B})
    # (A and B) given A, B via (TRUE and TRUE)
    AeqT.lhsSubstitute(Function(And(X, B), [X])).prove({A, B})
    # forall_{A | A, B | B} (A and B)
    return And(A, B).generalize([A, B], [A, B]).qed()
booleans.deriveOnDemand('conjunctionIntro', conjunctionIntroDerivation)

# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
def unfoldInBoolDerivation():
    from sets import sets, In, Singleton
    from equality import Equals, y, X
    # [A in ({TRUE} union {FALSE})] given inBool(A)
    AinTunionF = booleans.boolsDef.rhsSubstitute(Function(In(A, X), [X])).prove({inBool(A)})
    # (A in {TRUE}) or (A in {FALSE}) given inBool(A)
    AinTunionF.unfold().prove({inBool(A)})
    # A=TRUE or (A in {FALSE}) given inBool(A)
    sets.singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({inBool(A)})
    # A=TRUE or A=FALSE given inBool(A)
    conclusion = sets.singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(Function(Or(Equals(A, TRUE), X), [X])).prove({inBool(A)})
    # forall_{A} inBool(A) => (A=TRUE or A=FALSE)
    return Implies(inBool(A), conclusion).generalize([A]).qed()
booleans.deriveOnDemand('unfoldInBool', unfoldInBoolDerivation)

# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
def foldInBoolDerivation():
    from sets import sets, In, Singleton, Union
    from equality import Equals, y, X
    # hypothesis = (A=TRUE or A=FALSE)
    hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
    # (A=TRUE) or (A in {FALSE}) given hypothesis
    sets.singletonDef.specialize({x:A, y:FALSE}).lhsSubstitute(Function(Or(Equals(A, TRUE), X), [X])).prove({hypothesis})
    # (A in {TRUE}) or (A in {FALSE}) given hypothesis
    sets.singletonDef.specialize({x:A, y:TRUE}).lhsSubstitute(Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({hypothesis})
    # [A in ({TRUE} union {FALSE})] given hypothesis
    In(A, Union(Singleton(TRUE), Singleton(FALSE))).proveAsFolded()
    # (A in BOOLEANS) given hypothesis
    booleans.boolsDef.lhsSubstitute(Function(In(A, X), [X])).prove({hypothesis})
    # forall_{A} (A=TRUE or A=FALSE) => inBool(A)
    return Implies(hypothesis, inBool(A)).generalize([A]).qed()
booleans.deriveOnDemand('foldInBool', foldInBoolDerivation)

# forall_{A} Not(A) => [A => FALSE]
def contradictionFromNegationDerivation():
    # FALSE given Not(A) and A
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
    # Not(A) given A=FALSE because Not(FALSE)
    notA = AeqF.lhsSubstitute(Function(Not(X), [X])).prove({AeqF})
    return Implies(AeqF, notA).generalize([A]).qed()
booleans.deriveOnDemand('notFromEqFalse', notFromEqFalseDerivation)

# forall_{A} (FALSE=A) => Not(A)
def notFromEqFalseRevDerivation():
    from equality import Equals
    # FeqA := (F=A)
    FeqA = Equals(FALSE, A)
    # Not(A) given FeqA
    notA = FeqA.deriveReversed().deriveFromBooleanEquality().prove({FeqA})
    return Implies(FeqA, notA).generalize([A]).qed()
booleans.deriveOnDemand('notFromEqFalseRev', notFromEqFalseRevDerivation)

# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
def notOrFromNeitherDerivation():
    # Not(A or B) = Not(F or B) given Not(A)
    notAorB_eq_notForB = Not(A).equateNegatedToFalse().substitution(Function(Not(Or(X, B)), [X])).prove({Not(A)})
    # Not(A or B) = Not(F or F) given Not(A), Not(B)
    notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(Not(B).equateNegatedToFalse().substitution(Function(Not(Or(FALSE, X)), [X]))).prove({Not(A), Not(B)})
    #  Not(A or B) = Not(F) given Not(A), Not(B)
    notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(booleans.orFF.substitution(Function(Not(X), [X]))).prove({Not(A), Not(B)})
    # Not(FALSE)
    booleans.notFalse
    # Not(A or B) given Not(A), Not(B)
    notAorB = notAorB_eq_notF.deriveLeftViaEquivalence().prove({Not(A), Not(B)})
    # forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
    return Implies(Not(A), Implies(Not(B), notAorB)).generalize([A, B]).qed()
booleans.deriveOnDemand('notOrFromNeither', notOrFromNeitherDerivation)

# forall_{A, B | Not(A), Not(B)} (A or B) => FALSE
def orContradictionDerivation():
    # (A or B) => FALSE given Not(A), Not(B)
    AorB_impl_F = booleans.notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()
    return AorB_impl_F.generalize([A, B], [Not(A), Not(B)]).qed()    
booleans.deriveOnDemand('orContradiction', orContradictionDerivation)

# forall_{A, B | inBool(A), Not(B)} (A or B) => A
def orImpliesLeftIfNotRightDerivation():
    # (A or B) => FALSE given Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: A given isBool(A), A or B, Not(B)
    Implies(Not(A), FALSE).deriveHypotheticalContradiction().prove({inBool(A), Or(A, B), Not(B)})
    # forall_{A, B | isBool(A), Not(B)} (A or B) => A
    return Implies(Or(A, B), A).generalize([A, B], [inBool(A), Not(B)]).qed()
booleans.deriveOnDemand('orImpliesLeftIfNotRight', orImpliesLeftIfNotRightDerivation)

# forall_{A, B | Not(A), inBool(B)} (A or B) => B
def orImpliesRightIfNotLeftDerivation():    
    # (A or B) => FALSE given Not(A), Not(B)
    booleans.orContradiction.specialize().prove({Not(A), Not(B)})
    # By contradiction: B given isBool(B), (A or B), Not(A)
    Implies(Not(B), FALSE).deriveHypotheticalContradiction().prove({inBool(B), Or(A, B), Not(A)})
    # forall_{A, B | Not(A), inBool(B)} (A or B) => B
    return Implies(Or(A, B), B).generalize([A, B], [Not(A), inBool(B)]).qed()
booleans.deriveOnDemand('orImpliesRightIfNotLeft', orImpliesRightIfNotLeftDerivation)

# forall_{A} A => Not(Not(A))
def doubleNegationDerivation():
    # A=TRUE given A
    AeqT = deriveStmtEqTrue(A)
    # [Not(A)=FALSE] given A=TRUE
    AeqT.substitution(Function(Not(X), [X])).applyTransitivity(booleans.notT).prove({AeqT})
    # [Not(A)=FALSE] => Not(Not(A))
    booleans.notFromEqFalse.specialize({A:Not(A)}).prove()
    # forall_{A} A => Not(Not(A))
    return Implies(A, Not(Not(A))).generalize([A]).qed()
booleans.deriveOnDemand('doubleNegation', doubleNegationDerivation)

# forall_{A} A => [Not(A)=FALSE]
def eqFalseFromNegationDerivation():
    # Not(Not(A)) given A
    notNotA = Not(Not(A)).proveByDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse()).generalize([A]).qed()
booleans.deriveOnDemand('eqFalseFromNegation', eqFalseFromNegationDerivation)

# forall_{A} A => [FALSE=Not(A)]
def eqFalseRevFromNegationDerivation():
    # Not(Not(A)) given A
    notNotA = Not(Not(A)).proveByDoubleNegation()
    return Implies(A, notNotA.equateNegatedToFalse().deriveReversed()).generalize([A]).qed()
booleans.deriveOnDemand('eqFalseRevFromNegation', eqFalseRevFromNegationDerivation)

# forall_{A | inBool(A)} Not(Not(A)) => A
def fromDoubleNegationDerivation():
    # hypothesis = Not(Not(A))
    hypothesis = booleans.state(Not(Not(A)))
    # FALSE given Not(A), Not(Not(A))
    hypothesis.equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), hypothesis})
    # [Not(A) => FALSE] => A given isBool(A)
    booleans.hypotheticalContraNegation.specialize().prove({inBool(A)})
    # isBool(A) => [Not(Not(A)) => A] via hypothetical reasoning
    return Implies(hypothesis, A).generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('fromDoubleNegation', fromDoubleNegationDerivation)

# forall_{A | inBool(A)} (A != FALSE) => A
def fromNotFalseDerivation():
    from equality import NotEquals
    # AnotF = (A != FALSE)
    AnotF = NotEquals(A, FALSE)
    # notAeqF = Not(A = FALSE)
    notAeqF = AnotF.unfold()
    # (A=TRUE or A=FALSE) given inBool(A)
    AeqT_or_AeqF = inBool(A).unfold()
    AeqT = AeqT_or_AeqF.operands[0]
    # Not(A=FALSE) and (A=TRUE or A=FALSE) given each
    compose(notAeqF, AeqT_or_AeqF).prove({AnotF, AeqT_or_AeqF})
    # inBool(A=TRUE)
    AeqT.eqInBool()
    # A given isBool(A), Not(A=FALSE)
    AeqT_or_AeqF.deriveLeftIfNotRight().deriveFromBooleanEquality().prove({inBool(A), AnotF})
    # forall_{A | isBool(A)} Not(A=FALSE) => A
    return Implies(AnotF, A).generalize([A], [inBool(A)]).qed()
booleans.deriveOnDemand('fromNotFalse', fromNotFalseDerivation)

# forall_{A, B | inBool(B)} [Not(B) => Not(A)] => [A=>B] 
def transpositionFromNegatedDerivation():
    # Contradiction proof of B given (Not(B)=>Not(A)), A, and isBool(B)
    notBimplNotA = booleans.state(Implies(Not(B), Not(A)))
    # A=FALSE given Not(B)=>Not(A) and Not(B)
    AeqF = notBimplNotA.deriveConclusion().equateNegatedToFalse().prove({notBimplNotA, Not(B)})
    # FALSE given Not(B)=>Not(A), Not(B), and A
    AeqF.deriveRightViaEquivalence().prove({notBimplNotA, Not(B), A})
    # B given isBool(B), (Not(B)=>Not(A)), A
    Implies(Not(B), FALSE).deriveHypotheticalContradiction().prove({inBool(B), notBimplNotA, A})
    # [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming isBool(B)
    transpositionExpr = Implies(notBimplNotA, Implies(A, B)).prove({inBool(B)})
    # forall_{A, B | isBool(B)} [A => B] => [Not(B) => Not(A)]
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
booleans.deriveOnDemand('transpositionFromNegated', transpositionFromNegatedDerivation)

# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
def doubleNegateConclusionDerivation():
    # Not(Not(B)) given B and isBool(B)
    notNotB = Not(Not(B)).proveByDoubleNegation()
    # [A=>B] => [A => Not(Not(B))] given isBool(B)
    innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
    # forall_{A, B | isBool(B)}  [A=>B] => [A => Not(Not(B))]
    return innerExpr.generalize([A, B], [inBool(B)]).qed()
booleans.deriveOnDemand('doubleNegateConclusion', doubleNegateConclusionDerivation)

# forall_{A, B | isBool(A), isBool(B)} [Not(B) => A] => [Not(A)=>B] 
def transpositionFromNegatedHypothesisDerivation():
    # [Not(B) => Not(Not(A))] => [Not(A) => B)]  given isBool(B)
    toConclusion = Implies(Not(B), Not(Not(A))).transposition()
    # [Not(B) => A] => [Not(B) => Not(Not(A))] given isBool(A)    
    fromHyp = booleans.doubleNegateConclusion.specialize({A:Not(B), B:A}).prove({inBool(A)})
    # [Not(B) => A] => [Not(A)=>B] given isBool(A) and isBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | isBool(A), isBool(B)} [Not(B) => A] => [Not(A)=>B] 
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('transpositionFromNegatedHypothesis', transpositionFromNegatedHypothesisDerivation)

# forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
def transpositionFromNegatedConclusionDerivation():
    from equality import Equals, NotEquals
    # isBool(B=FALSE)
    Equals(B, FALSE).eqInBool()
    # [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using isBool(B=FALSE)
    midPointBackHalf = Implies(Not(Equals(B, FALSE)), Not(A)).transposition()
    # [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
    midPointFrontHalf = NotEquals(B, FALSE).definition().rhsStatementSubstitution(Function(Implies(X, Not(A)), [X])).prove()
    # [(B != FALSE) => Not(A)] => [A => (B=FALSE)]
    midPoint = midPointFrontHalf.applySyllogism(midPointBackHalf).prove()
    # B given B != FALSE) and isBool(B)
    notBeqF = NotEquals(B, FALSE)
    notBeqF.deriveFromDoubleNegation().prove({notBeqF, inBool(B)})
    # [B => Not(A)] => [(B != FALSE) => Not(A)] given isBool(B)
    fromHyp = Implies(Implies(B, Not(A)), Implies(notBeqF, Not(A))).prove({inBool(B)})
    # Not(B) given B=FALSE
    BeqF = Equals(B, FALSE)
    BeqF.deriveFromBooleanEquality().prove({BeqF})
    # [A => (B=FALSE)] => [A => Not(B)] given isBool(B)
    toConclusion = Implies(Implies(A, BeqF), Implies(A, Not(B))).prove({inBool(B)})
    # [B => Not(A)] => [A=>Not(B)] given isBool(B)
    transpositionExpr = fromHyp.applySyllogism(midPoint).applySyllogism(toConclusion).prove({inBool(B)})
    # forall_{A, B | isBool(B)} [B => Not(A)] => [A=>Not(B)] 
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
booleans.deriveOnDemand('transpositionFromNegatedConclusion', transpositionFromNegatedConclusionDerivation)

# forall_{A, B | isBool(A), isBool(B)} [B=>A] => [Not(A) => Not(B)] 
def transpositionToNegatedDerivation():
    # [B => Not(Not(A))] => [Not(A)=>Not(B)] given isBool(A), isBool(B)
    toConclusion = Implies(B, Not(Not(A))).transposition()
    # [B => A] => [B => Not(Not(A))] given isBool(A)
    fromHyp = booleans.doubleNegateConclusion.specialize({A:B, B:A}).prove({inBool(A)})
    # [B => A] => [Not(A)=>Not(B)] given isBool(A), isBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | isBool(A), isBool(B)} [B=>A] => [Not(A) => Not(B)] 
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
booleans.deriveOnDemand('transpositionToNegated', transpositionToNegatedDerivation)

# TRUE != FALSE
booleans.deriveOnDemand('trueNotFalse', lambda : booleans.falseNotTrue.deriveReversed().qed())

# forall_{A} A => (A != FALSE)
def notEqualsFalseDerivation():
    from equality import NotEquals
    # A=TRUE given A
    AeqT = deriveStmtEqTrue(A)
    # TRUE != FALSE
    booleans.trueNotFalse
    # (A != FALSE) given A
    AnotF = AeqT.lhsSubstitute(Function(NotEquals(X, FALSE), [X])).prove({A})
    # forall_{A} A => (A != FALSE)
    return Implies(A, AnotF).generalize([A]).qed()
booleans.deriveOnDemand('notEqualsFalse', notEqualsFalseDerivation)

# inBool(TRUE)
def trueInBoolDerivation():
    from equality import Equals
    # [TRUE or FALSE] 
    booleans.orTF.deriveFromBooleanEquality().prove()
    # [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
    booleans.trueNotFalse.unfold().equateNegatedToFalse().lhsSubstitute(Function(Or(TRUE, X), [X])).prove()
    # [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
    deriveStmtEqTrue(booleans.trueEqTrue).lhsSubstitute(Function(Or(X, Equals(TRUE, FALSE)), [X])).prove()
    # inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
    return inBool(TRUE).proveAsFolded().qed()
booleans.deriveOnDemand('trueInBool', trueInBoolDerivation)

# inBool(FALSE)
def falseInBoolDerivation():
    from equality import Equals
    # [FALSE or TRUE] 
    booleans.orFT.deriveFromBooleanEquality().prove()
    # [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
    deriveStmtEqTrue(booleans.falseEqFalse).lhsSubstitute(Function(Or(FALSE, X), [X])).prove()
    # [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
    booleans.falseNotTrue.unfold().equateNegatedToFalse().lhsSubstitute(Function(Or(X, Equals(FALSE, FALSE)), [X])).prove()
    # isBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
    return inBool(FALSE).proveAsFolded().qed()
booleans.deriveOnDemand('falseInBool', falseInBoolDerivation)

# forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
def hypotheticalDisjunctionDerivation():
    AorB = Or(A, B)
    hypothesis = And(Implies(A, C), Implies(B, C))
    ABCareBoolInOrder = [inBool(A), inBool(B), inBool(C)]
    ABCareBool = set(ABCareBoolInOrder)
    # A=>C, B=>C given (A=>C and B=>C)
    AimplC, _ = hypothesis.decompose()
    # Not(A) given inBool(A), inBool(B), (A=>C and B=>C), Not(C)
    AimplC.transpose().deriveConclusion().prove({inBool(A), inBool(C), hypothesis, Not(C)})
    # B given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    AorB.deriveRightIfNotLeft().prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # Not(TRUE) given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    deriveStmtEqTrue(C).rhsSubstitute(Function(Not(X), [X])).prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # FALSE given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    booleans.notT.deriveRightViaEquivalence().prove(ABCareBool | {hypothesis, AorB, Not(C)})
    # Contradiction proof of C given (A=>C and B=>C), (A or B), isBool(A), and isBool(B)
    Implies(Not(C), FALSE).deriveHypotheticalContradiction().prove(ABCareBool | {hypothesis, AorB})
    return Implies(hypothesis, Implies(AorB, C)).generalize([A, B, C], ABCareBoolInOrder).qed()
booleans.deriveOnDemand('hypotheticalDisjunction', hypotheticalDisjunctionDerivation)

# forall_{P} [P(TRUE) and P(FALSE)] => {forall_{A in BOOLEANS} P(A) = TRUE}
def forallBoolEvalTrueDerivation():
    from equality import Equals
    # hypothesis = [P(TRUE) and P(FALSE)]
    hypothesis = And(PofTrue, PofFalse)
    # inBool(A=TRUE), inBool(A=FALSE), inBool(P(A) = TRUE)
    AeqT = Equals(A, TRUE)
    AeqF = Equals(A, FALSE)
    PofAeqT = Equals(PofA, TRUE)
    for eqExpr in (AeqT, AeqF, PofAeqT):
        eqExpr.eqInBool()
    # P(TRUE), P(FALSE) given hypothesis
    for case in hypothesis.decompose(): case.prove({hypothesis})
    # [A=TRUE => P(A)=TRUE and A=FALSE => P(A)=TRUE] => [(A=TRUE or A=FALSE) => P(A)=TRUE]
    specDisj = booleans.hypotheticalDisjunction.specialize({A:AeqT, B:AeqF, C:PofAeqT}).prove()
    # A=TRUE => P(A)=TRUE given hypothesis
    AeqTimplPofA = Implies(AeqT, deriveStmtEqTrue(AeqT.lhsSubstitute(Function(PofA, [A])))).prove({hypothesis})
    # A=FALSE => P(A)=TRUE given hypothesis
    AeqFimplPofA = Implies(AeqF, deriveStmtEqTrue(AeqF.lhsSubstitute(Function(PofA, [A])))).prove({hypothesis})
    # [A=TRUE => P(A) and A=FALSE => P(A)=TRUE] given hypothesis
    compose(AeqTimplPofA, AeqFimplPofA).prove({hypothesis})
    # [(A=TRUE or A=FALSE) => P(A)=TRUE] given hypothesis
    AeqTorAeqFimplPofAeqT = specDisj.deriveConclusion().prove({hypothesis})
    # (A=TRUE or A=FALSE) => P(A)
    Implies(AeqTorAeqFimplPofAeqT.hypothesis, AeqTorAeqFimplPofAeqT.deriveConclusion().deriveFromBooleanEquality()).prove({hypothesis})
    # forall_{A in BOOLEANS} P(A) given hypothesis
    conclusion = PofA.generalize([A], [inBool(A).proveAsFolded()]).prove({hypothesis})
    # forall_{P} P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
    return Implies(hypothesis, deriveStmtEqTrue(conclusion)).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalTrue', forallBoolEvalTrueDerivation)

# forall_{P} [P(TRUE) = FALSE] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
def forallBoolEvalFalseViaTrueDerivation():
    from equality import Equals
    # hypothesis = [P(TRUE) = FALSE]
    hypothesis = Equals(PofTrue, FALSE)
    # (TRUE in BOOLEANS and Not(P(TRUE)) => Not(forall_{A in BOOLEANS} P(A))}
    notForallBool = booleans.forallNegation.specialize({Q:Function(inBool(X), [X]), x:TRUE}).relabeled({y:A}).prove().conclusion
    # (TRUE in BOOLEANS and Not(P(TRUE)) given hypothesis
    compose(booleans.trueInBool, hypothesis.deriveFromBooleanEquality()).prove({hypothesis})
    # forall_{P} [P(TRUE) = FALSE] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, notForallBool.equateNegatedToFalse()).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalFalseViaTrue', forallBoolEvalFalseViaTrueDerivation)

# forall_{P} {P(FALSE) = FALSE} => {[forall_{A in BOOLEANS} P(A)] = FALSE}
def forallBoolEvalFalseViaFalseDerivation():
    from equality import Equals
    # hypothesis = [P(FALSE) = FALSE]
    hypothesis = Equals(PofFalse, FALSE)
    # (FALSE in BOOLEANS and Not(P(FALSE)) => Not(forall_{A in BOOLEANS} P(A))}
    notForallBool = booleans.forallNegation.specialize({Q:Function(inBool(X), [X]), x:FALSE}).relabeled({y:A}).prove().conclusion
    # (FALSE in BOOLEANS and Not(P(FALSE)) given hypothesis
    compose(booleans.falseInBool, hypothesis.deriveFromBooleanEquality()).prove({hypothesis})
    # forall_{P} [P(FALSE) = FALSE] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, notForallBool.equateNegatedToFalse()).generalize([P]).qed()
booleans.deriveOnDemand('forallBoolEvalFalseViaFalse', forallBoolEvalFalseViaFalseDerivation)
