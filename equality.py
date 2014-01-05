from proveItCore import *
from genericOperations import *

f = Variable('f')
g = Variable('g')
P = Variable('P')
Q = Variable('Q')
a = Variable('a')
b = Variable('b')
c = Variable('c')
x = Variable('x')
y = Variable('y')
z = Variable('z')
fa = Operation(f, [a])
fb = Operation(f, [b])
fab = Operation(f, [a, b])
fx = Operation(f, [x])
fy = Operation(f, [y])
fxy = Operation(f, [x, y])
gx = Operation(g, [x])
Px = Operation(P, [x])
Py = Operation(P, [y])
Qx = Operation(Q, [x])
X = Variable('X')
Upsilon = Variable('Upsilon', {MATHML:'&#x03C5;'})

class EqualityContext(Context):
    def __init__(self):
        Context.__init__(self, 'EQUALITY')

    def stateAxioms(self):
        """
        Generates the equality axioms.  Because of the interdependence of booleans, 
        equality, and sets, this is executed on demand after these have all loaded.
        """
        from booleans import Forall, inBool, Implies, Not
        
        # forall_{x, y} inBool(x = y)
        self.equalityInBool = self.stateAxiom(Forall([x, y], inBool(Equals(x, y))))
        
        # forall_{x, y, z} (x=y) => [(y=z) => (x=z)]
        self.equalsTransitivity = self.stateAxiom(Forall([x, y, z], Implies(Equals(x, y), Implies(Equals(y, z), Equals(x, z)))))
        # forall_{x} x=x
        self.equalsReflexivity = self.stateAxiom(Forall([x], Equals(x, x)))
        # forall_{x, y} x=y => y=x
        self.equalsSymmetry = self.stateAxiom(Forall([x, y], Implies(Equals(x, y), Equals(y, x))))
        
        # forall_{x, y} [x != y] = Not([x = y])
        self.notEqualsDef = self.stateAxiom(Forall([x, y], Equals(NotEquals(x, y), Not(Equals(x, y)))))
        
        # forall_{f, x, y} [(x=y) => f(x)=f(y)]
        self.substitution = self.stateAxiom(Forall([f, x, y], Implies(Equals(x, y), Equals(fx, fy))))      
        
        # forall_{f, g, Q, Upsilon} [forall_{x | Q(x)} f(x) = g(x)] => {[Upsilon_{x | Q(x) f(x)] = [Upsilon_{x | Q(x) g(x)]}
        self.instanceSubstitution = self.stateAxiom(Forall([f, g, Q, Upsilon], Implies(Forall([x], Equals(fx, gx), [Qx]), Equals(OperationOverInstances(Upsilon, x, fx, Qx), OperationOverInstances(Upsilon, x, gx, Qx)))))

equality = EqualityContext()

# equality is an important core concept
EQUALS = equality.addLiteral('EQUALS')
NOTEQUALS = equality.addLiteral('NOTEQUALS')

class Equals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, EQUALS, a, b)
        self.lhs = a
        self.rhs = b

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '='
        else:
            return '<mo>=</mo>'

    def remake(self, operator, operands):
        if operator == EQUALS and len(operands) == 2:
            return Equals(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
    
    def concludeViaReflexivity(self):
        '''
        Prove and return self of the form x = x.
        '''
        assert self.lhs == self.rhs
        return equality.equalsReflexivity.specialize({x:self.lhs}).check()
            
    def deriveReversed(self):
        '''
        From x = y derive y = x.
        '''
        return equality.equalsSymmetry.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().check({self})

    def transitivityImpl(self, otherEquality):
        '''
        From x = y (self) and the given y = z (otherEquality) derive and return 
        (y=z) => (x = z).
        Also works more generally as long as there is a common side to the equations.
        '''
        assert isinstance(otherEquality, Equals)
        if self.rhs == otherEquality.lhs:
            # from x = y, y = z, derive x = z
            result = equality.equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}).deriveConclusion()
            return result.check({self})
        elif self.lhs == otherEquality.lhs:
            # from y = x and y = z, derive x = z
            return self.deriveReversed().transitivityImpl(otherEquality)
        elif self.lhs == otherEquality.rhs:
            # from y = x and z = y, derive x = z
            return self.deriveReversed().transitivityImpl(otherEquality.deriveReversed())
        elif self.rhs == otherEquality.rhs:
            # from x = y and z = y, derive x = z
            return self.transitivityImpl(otherEquality.deriveReversed())
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
            
    def applyTransitivity(self, otherEquality):
        '''
        From x = y (self) and y = z (otherEquality) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        '''
        return self.transitivityImpl(otherEquality).deriveConclusion().check({self, otherEquality})
        
    def deriveViaBooleanEquality(self):
        '''
        From A = TRUE or TRUE = A derive A, or from A = FALSE or FALSE = A derive Not(A).
        Note, see deriveStmtEqTrue or Not.equateNegatedToFalse for the reverse process.
        '''
        from booleans import booleans, TRUE, FALSE, A
        if self.lhs == TRUE:
            return booleans.eqTrueRevElim.specialize({A:self.rhs}).deriveConclusion().check({self}) # A
        elif self.rhs == TRUE:
            return booleans.eqTrueElim.specialize({A:self.lhs}).deriveConclusion().check({self}) # A
        elif self.lhs == FALSE:
            return booleans.notFromEqFalseRev.specialize({A:self.rhs}).deriveConclusion().check({self}) # Not(A)            
        elif self.rhs == FALSE:
            return booleans.notFromEqFalse.specialize({A:self.lhs}).deriveConclusion().check({self}) # Not(A)
    
    def concludeBooleanEquality(self):
        '''
        Prove and return self of the form (A=TRUE) assuming A, (TRUE=A) assuming A, 
        A=FALSE assuming Not(A), FALSE=A assuming Not(A), [Not(A)=FALSE] assuming A, or [FALSE=Not(A)] assuming A.
        '''
        from booleans import booleans, TRUE, FALSE, A, Not
        if self.rhs == TRUE:
            return booleans.eqTrueIntro.specialize({A:self.lhs}).deriveConclusion().check({self.lhs})
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                return booleans.eqFalseFromNegation.specialize({A:self.lhs.operand}).deriveConclusion().check({self.lhs.operand})
            else:
                return Not(self.lhs).equateNegatedToFalse()
        elif self.lhs == TRUE:
            return booleans.eqTrueRevIntro.specialize({A:self.rhs}).deriveConclusion().check({self.rhs})
        elif self.lhs == FALSE:
            if isinstance(self.rhs, Not):
                return booleans.eqFalseRevFromNegation.specialize({A:self.rhs.operand}).deriveConclusion().check({self.rhs.operand})
            else:
                return Not(self.rhs).equateFalseToNegated()
    
    def deriveIsInSingleton(self):
        '''
        From (x = y), derive (x in {y}).
        '''
        from sets import sets
        sets.singletonDef.specialize({x:self.lhs, y:self.rhs}).deriveLeft().check({self})
    
    def substitution(self, function):
        '''
        From x = y, and given a function f(x), derive f(x)=f(y).
        '''
        assert isinstance(function, Function) or isinstance(function, Variable) or isinstance(function, Literal)
        subMap = SubstitutionMap({x:self.lhs, y:self.rhs, f:function})
        return equality.substitution.specialize(subMap).deriveConclusion().check({self})
        
    def lhsStatementSubstitution(self, function):
        '''
        From x = y, and given a function P(x), derive P(y)=>P(x).
        '''
        assert isinstance(function, Function) or isinstance(function, Variable) or isinstance(function, Literal)        
        return equality.lhsSubstitution.specialize({x:self.lhs, y:self.rhs, P:function}).deriveConclusion().check({self})
    
    def rhsStatementSubstitution(self, function):
        '''
        From x = y, and given a function P(x), derive P(x)=>P(y).
        '''
        assert isinstance(function, Function) or isinstance(function, Variable) or isinstance(function, Literal)        
        return equality.rhsSubstitution.specialize({x:self.lhs, y:self.rhs, P:function}).deriveConclusion().check({self})

    def lhsSubstitute(self, function):
        '''
        From x = y, and given a function P(x), derive P(x) assuming P(y)
        '''
        substitution = self.lhsStatementSubstitution(function)
        return substitution.deriveConclusion().check({self, substitution.hypothesis})
        
    def rhsSubstitute(self, function):
        '''
        From x = y, and given a function P(x), derive P(y) assuming P(x)
        '''
        substitution = self.rhsStatementSubstitution(function)
        return substitution.deriveConclusion().check({self, substitution.hypothesis})

    def leftImplViaEquivalence(self):
        '''
        From A = B, derive B=>A
        '''
        return self.lhsStatementSubstitution(Function(X, [X])).check({self})

    def rightImplViaEquivalence(self):
        '''
        From A = B, derive A=>B
        '''
        return self.rhsStatementSubstitution(Function(X, [X])).check({self})
        
    def deriveRightViaEquivalence(self):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        return self.rhsSubstitute(Function(X, [X])).check({self, self.lhs})

    def deriveLeftViaEquivalence(self):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        return self.lhsSubstitute(Function(X, [X])).check({self, self.rhs})
    
    def deduceInBool(self):
        '''
        Deduce and return that this equality statement is in the set of BOOLEANS.
        '''
        return equality.equalityInBool.specialize({x:self.lhs, y:self.rhs}).check()
    
    def inBoolViaBooleanEquality(self):
        '''
        From A=TRUE, A=FALSE, TRUE=A, or FALSE=A, derive and return inBool(A).
        '''
        from booleans import booleans, TRUE, FALSE, A
        if self.rhs == TRUE:
            return booleans.inBoolIfEqTrue.specialize({A:self.lhs}).deriveConclusion().prove({self})
        if self.lhs == TRUE:
            return booleans.inBoolIfEqTrueRev.specialize({A:self.rhs}).deriveConclusion().prove({self})
        if self.rhs == FALSE:
            return booleans.inBoolIfEqFalse.specialize({A:self.lhs}).deriveConclusion().prove({self})
        if self.lhs == FALSE:
            return booleans.inBoolIfEqFalseRev.specialize({A:self.rhs}).deriveConclusion().prove({self})
    
    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to TRUE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from booleans import booleans, TRUE
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            if self.lhs == self.rhs:
                # simple case where both sides are the same, use reflexivity
                return Equals(self.concludeViaReflexivity(), TRUE).concludeBooleanEquality()
            
            # evaluate both sides and see if simplification is possible
            lhsSimpl = self.lhs
            rhsSimpl = self.rhs
            try:
                lhsEval = self.lhs.evaluate()
                lhsSimpl = lhsEval.rhs
            except AttributeError:
                lhsEval = None
            try:
                rhsEval = self.rhs.evaluate()
                rhsSimpl = rhsEval.rhs
            except AttributeError:
                rhsEval = None
    
            if lhsEval == None and rhsEval == None:
                # Cannot simplify further.  Use evalEquality.
                return lhsSimpl.evalEquality(rhsSimpl)
            else:         
                # evaluate the simplified version
                simplEval = Equals(lhsSimpl, rhsSimpl).evaluate()
                val = simplEval.rhs
                # Using substitution, go from simplEval to self=val
                if lhsEval != None:
                    lhsEval.lhsSubstitute(Function(Equals(Equals(X, rhsSimpl), val), [X]))
                if rhsEval != None:
                    rhsEval.lhsSubstitute(Function(Equals(Equals(self.lhs, X), val), [X]))
                return Equals(self, val)
            
        return booleans.evaluate(self, doEval)
        
class NotEquals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, NOTEQUALS, a, b)
        self.lhs = a
        self.rhs = b
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '!='
        elif formatType == MATHML:
            return '<mo>&#x2260;</mo>'

    def remake(self, operator, operands):
        if operator == NOTEQUALS and len(operands) == 2:
            return NotEquals(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
        
    def deriveReversed(self):
        '''
        From x != y derive y != x.
        '''
        return equality.notEqualsSymmetry.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().check({self})

    def deriveViaDoubleNegation(self):
        '''
        From A != FALSE, derive and return A assuming inBool(A).
        Also see version in Not class.
        '''
        from booleans import booleans, inBool, A, FALSE
        if self.rhs == FALSE:
            return booleans.fromNotFalse.specialize({A:self.lhs}).deriveConclusion().check({self, inBool(self.lhs)})

    def concludeViaDoubleNegation(self):
        '''
        Prove and return self of the form A != FALSE assuming A.
        Also see version in Not class.
        '''
        from booleans import booleans, FALSE, A
        if self.rhs == FALSE:
            return booleans.notEqualsFalse.specialize({A:self.lhs}).deriveConclusion().check({self.lhs})

    def definition(self):
        '''
        Return (x != y) = Not(x=y) where self represents (x != y).
        '''
        return equality.notEqualsDef.specialize({x:self.lhs, y:self.rhs}).check()

    def unfold(self):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        return equality.unfoldNotEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().check({self})

    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to TRUE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from booleans import booleans
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            unfoldedEvaluation = self.unfold().evaluate()
            return self.definition().lhsSubstitute(Function(Equals(X, unfoldedEvaluation.rhs), [X]))
        return booleans.evaluate(self, doEval)    

    def deduceInBool(self):
        '''
        Deduce and return that this 'not equals' statement is in the set of BOOLEANS.
        '''
        return equality.notEqualsInBool.specialize({x:self.lhs, y:self.rhs}).check()
    

# Using substitution

# forall_{P, x, y} {(x=y) => [P(y) => P(x)]}
def lhsSubstitutionDerivation():
    from booleans import Implies, deriveStmtEqTrue
    # hypothesis = (x=y)
    hypothesis = Equals(x, y)
    # P(x) = P(y) assuming (x=y)
    Px_eq_Py = hypothesis.substitution(Function(Px, [x])).prove({hypothesis})
    # P(x) assuming (x=y), P(y)
    deriveStmtEqTrue(Py).applyTransitivity(Px_eq_Py).deriveViaBooleanEquality().prove({hypothesis, Py})
    # forall_{P, x, y} {(x = y) => [P(x) => P(y)]}, by (nested) hypothetical reasoning
    return Implies(Equals(x, y), Implies(Py, Px)).generalize([P, x, y]).qed()
equality.deriveOnDemand('lhsSubstitution', lhsSubstitutionDerivation)

# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
def rhsSubstitutionDerivation():
    from booleans import Implies
    # hypothesis = (x=y)
    hypothesis = Equals(x, y)
    # P(x) assuming x=y and P(y)
    hypothesis.deriveReversed().lhsSubstitute(Function(Px, [x])).prove({hypothesis, Py})
    # forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
    return Implies(hypothesis, Implies(Px, Py)).generalize([P, x, y]).qed()
equality.deriveOnDemand('rhsSubstitution',  rhsSubstitutionDerivation)

# Evaluations

# forall_{f, x, a, c} (x=a) => {[f(a)=c] => [f(x)=c]}
def unaryEvaluationDerivation():
    from booleans import Implies
    # hypothesis = (x=a)
    hypothesis = Equals(x, a)
    # [f(x) = f(a)] assuming x=a
    fx_eq_fa = hypothesis.substitution(Function(fx, [x])).prove({hypothesis})
    # [f(a)=c] => [f(x)=c] assuming x=a
    conclusion = fx_eq_fa.transitivityImpl(Equals(fa, c)).prove({hypothesis})
    # forall_{f, x, a, c} (x=a) => {[f(a)=c] => [f(x)=c]}
    return Implies(hypothesis, conclusion).generalize([f, x, a, c]).qed()
equality.deriveOnDemand('unaryEvaluation', unaryEvaluationDerivation)  

# forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
def binarySubstitutionDerivation():
    from booleans import And, Implies
    # hypothesis = (x=a and y=b)
    hypothesis = And(Equals(x, a), Equals(y, b))
    # f(x, y) = f(a, y) assuming hypothesis
    fxy_eq_fay = hypothesis.deriveLeft().substitution(Function(fxy, [x])).prove({hypothesis})
    # f(a, y) = f(a, b) assuming hypothesis
    fay_eq_fab = hypothesis.deriveRight().substitution(Function(fab, [b])).prove({hypothesis})
    # f(x, y) = f(a, b) assuming hypothesis
    conclusion = fxy_eq_fay.applyTransitivity(fay_eq_fab).prove({hypothesis})
    # forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
    return Implies(hypothesis, conclusion).generalize([f, x, y, a, b]).qed()
equality.deriveOnDemand('binarySubstitution', binarySubstitutionDerivation)  

# forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
def binaryEvaluationDerivation():
    from booleans import And, Implies
    # hypothesis = (x=a and y=b)
    hypothesis = And(Equals(x, a), Equals(y, b))
    # [f(x, y) = f(a, b)] assuming hypothesis
    fxy_eq_fab = equality.binarySubstitution.specialize().deriveConclusion().prove({hypothesis})
    # [f(a, b)=c] => [f(x, y)=c] assuming hypothesis
    conclusion = fxy_eq_fab.transitivityImpl(Equals(fab, c)).prove({hypothesis})
    # forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
    return Implies(hypothesis, conclusion).generalize([f, x, y, a, b, c]).qed()
equality.deriveOnDemand('binaryEvaluation', binaryEvaluationDerivation)

# forall_{x, y} [x != y] => Not([x = y])
equality.deriveOnDemand('unfoldNotEquals', lambda : equality.notEqualsDef.specialize().rightImplViaEquivalence().generalize([x, y]).qed())

# forall_{x, y} Not([x = y]) => [x != y]
equality.deriveOnDemand('foldNotEquals', lambda : equality.notEqualsDef.specialize().leftImplViaEquivalence().generalize([x, y]).qed())

# forall_{x, y} (x != y) => (y != x)
def notEqualsSymmetryDerivation():
    from booleans import Implies, Not
    # hypothesis = (x != y)
    hypothesis = NotEquals(x, y)
    # inBool(x=y)
    Equals(x, y).deduceInBool()
    # inBool(y=x)
    Equals(y, x).deduceInBool()
    # Not(x=y) => Not(y=x)
    equality.equalsSymmetry.specialize({x:y, y:x}).transpose().prove()
    # Not(x=y) assuming (x != y)
    NotEquals(x, y).unfold().prove({hypothesis})
    # (y != x) assuming Not(x = y)
    Not(Equals(y, x)).deriveNotEquals().prove({Not(Equals(y, x))})
    # forall_{x, y} (x != y) => (y != x)
    return Implies(hypothesis, NotEquals(y, x)).generalize([x, y]).qed()
equality.deriveOnDemand('notEqualsSymmetry', notEqualsSymmetryDerivation)

# forall_{x, y} (x != y) in BOOLEANS
def notEqualsInBoolDerivation():
    from booleans import Not, inBool
    # Not(x = y) in BOOLEANS
    Not(Equals(x, y)).deduceInBool().prove()
    # forall_{x, y} (x != y) in BOOLEANS
    return equality.notEqualsDef.specialize().lhsSubstitute(Function(inBool(X), [X])).generalize([x, y]).qed()
equality.deriveOnDemand('notEqualsInBool', notEqualsInBoolDerivation)
