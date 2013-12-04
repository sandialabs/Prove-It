from basicLogic import *
from sets import *

integers = Context('INTEGERS')

prevContext = Context.current
Context.current = integers

INTEGERS = integers.addLiteral('INTEGERS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x2124;</mtext><mspace/></mstyle>'})
NATURALS = integers.addLiteral('NATURALS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x2115;</mtext><mspace/></mstyle>'})
NON_NEGATIVES = integers.addLiteral('NON_NEGATIVES')
RECURSIVE_BINARY_OP = integers.addLiteral('RECURSIVE_BINARY_OP')
RECURSIVE_OP_OVER_INSTANCES = integers.addLiteral('RECURSIVE_OP_OVER_INSTANCES')
ZERO = integers.addLiteral('0')
ONE = integers.addLiteral('1')
TWO = integers.addLiteral('2')
THREE = integers.addLiteral('3')
FOUR = integers.addLiteral('4')
FIVE = integers.addLiteral('5')
SIX = integers.addLiteral('6')
SEVEN = integers.addLiteral('7')
EIGHT = integers.addLiteral('8')
NINE = integers.addLiteral('9')
TEN = integers.addLiteral('0xa')
ELEVEN = integers.addLiteral('0xb')
TWELVE = integers.addLiteral('0xc')
THIRTEEN = integers.addLiteral('0xd')
FOURTEEN = integers.addLiteral('0xe')
FIFTEEN = integers.addLiteral('0xf')
SIXTEEN = integers.addLiteral('0x10')

INFINITY = integers.addLiteral('INFINITY')

ADD = integers.addLiteral('ADD')
SUBTRACT = integers.addLiteral('SUBTRACT')
MULT = integers.addLiteral('MULT')
NEGATE = integers.addLiteral('NEGATE')

RANGE = integers.addLiteral('RANGE')

m = Variable('m')
n = Variable('n')
S = Variable('S')
P = Variable('P')
Pm = Operation(P, [m])
Pn = Operation(P, [n])
P0 = Operation(P, [ZERO])

class Add(AssociativeBinaryOperation):
    def __init__(self, m, n):
        AssociativeBinaryOperation.__init__(self, ADD, m, n)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '+'
        elif formatType == MATHML:
            return '<mo>+</mo>'

    def remake(self, operator, operands):
        if operator == ADD and len(operands) == 2:
            return Add(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

class Negate(Operation):
    def __init__(self, n):
        Operation.__init__(self, NEGATE, [n])

    def remake(self, operator, operands):
        if operator == NEGATE and len(operands) == 1:
            return Negate(operands[0])
        else:
            return Operation.remake(self, operator, operands)

class Subtract(Add):
    def __init__(self, m, n):
        if isinstance(n, Negate):
            Add.__init__(self, m, n.operands[0])
        else:
            Add.__init__(self, m, Negate(n))

    def remake(self, operator, operands):
        if operator == Add and len(operands) == 2:
            if isinstance(operands[1], Negate):
                return Subtract(operands[0], operands[1].operands[0])
            else:
                return Add(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

class Mult(AssociativeBinaryOperation):
    def __init__(self, m, n):
        Operation.__init__(self, MULT, m, n)

    def remake(self, operator, operands):
        if operator == MULT and len(operands) == 2:
            return Mult(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

class Range(Operation):
    def __init__(self, m, n):
        Operation.__init__(self, RANGE, [m, n])

    def remake(self, operator, operands):
        if operator == RANGE and len(operands) == 2:
            return Range(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

# This definition of integers is an implicit definition, but it is important that the
# definition ensures the minimum set that includes 0 and has closure upon adding 1 (counting).
# forall_S {[(0 in S) and (forall_{n} n in S => n+1 in S)] => S superset NATURALS}
integerDef = integers.stateAxiom(Forall([S], Implies(And(In(ZERO, S), Forall([n], In(Add(n, ONE), S), [In(n, S)])), Superset(S, NATURALS))))

# forall_P {[P(0) and forall_{n} P(n) => P(n+1)] => forall_{n in NATURALS} P(n)
def inductionLemmaDerivation():
    # hypothesis = [P(0) and forall_{n in NATURALS} P(n) => P(n+1)]
    hypothesis = And(P0, Forall([n], Implies(Pn, Operation(P, [Add(n, ONE)]))))
    # P(0) given hypothesis
    hypothesis.deriveLeft().prove({hypothesis})
    # P(n) => P(n+1) given hypothesis
    hypothesis.deriveRight().specialize().prove({hypothesis})
    # setSuchThatP = {m | P(m)}
    setSuchThatP = SetOfAll([m], m, suchThat=[Pm])
    # 0 in {m | P(m)} given hypothesis
    zeroInSetSuchThatP = setOfAllDef.specialize({x:ZERO, y:m}).deriveLeft().prove({hypothesis})
    # (n in {m | P(m)}) => P(n)
    setOfAllDef.specialize({x:n, y:m}).deriveRightImplication().prove({hypothesis})
    # (n+1 in {m | P(m)}) given (n in {m | P(m)}), hypothesis
    setOfAllDef.specialize({x:Add(n, ONE), y:m}).deriveLeft().prove({In(n, setSuchThatP), hypothesis})
    # [forall_{n in {m | P(m)}} (n+1 in {m | P(m)})] given hypothesis
    incrInSetSuchThatP = Implies(In(n, setSuchThatP), In(Add(n, ONE), setSuchThatP)).generalize([n], [In(n, setSuchThatP)]).prove({hypothesis})
    # (0 in {m | P(m)}) and [forall_{n} (n in {m | P(m)}) => (n+1 in {m | P(m)})] => {m | P(m)} given hypothesis
    compose(zeroInSetSuchThatP, incrInSetSuchThatP).prove({hypothesis})
    # n in NATURALS => n in {m | P(m)} given hypothesis
    integerDef.specialize({S:setSuchThatP}).deriveConclusion().unfold(n).specialize().prove({hypothesis})
    # nInNat = n in NATURALS
    nInNat = In(n, NATURALS)
    # forall_{n in NATURALS} P(n) given hypothesis
    conclusion = Implies(nInNat, Pn).generalize([n], [nInNat]).prove({hypothesis})
    # forall_P {[P(0) and forall_{n in NATURALS} P(n) => P(n+1)] => forall_{n in NATURALS} P(n)
    return Implies(hypothesis, conclusion).generalize([P]).qed()
inductionLemma = inductionLemmaDerivation()        

# forall_P {[P(0) and forall_{n in NATURALS} P(n) => P(n+1)] => forall_{n in NATURALS} P(n)
def inductionDerivation():
    # {[(0 in NATURALS and P(0)) and forall_{n} (n in NATURALS and P(n)) => (n+1 in NATURALS and P(n+1))] 
    #    => forall_{n in NATURALS} (n in NATURALS and P(n))
    inductionLemmaSpec = inductionLemma.specialize({P:Function(And(In(n, NATURALS), Pn), [n])})
           
"""
twoDef = integers.stateAxiom(Equals(Add(ONE, ONE), TWO))
threeDef = integers.stateAxiom(Equals(Add(TWO, ONE), THREE))
fourDef = integers.stateAxiom(Equals(Add(THREE, ONE), FOUR))
fiveDef = integers.stateAxiom(Equals(Add(FOUR, ONE), FIVE))
sixDef = integers.stateAxiom(Equals(Add(FIVE, ONE), SIX))
sevenDef = integers.stateAxiom(Equals(Add(SIX, ONE), SEVEN))
eightDef = integers.stateAxiom(Equals(Add(SEVEN, ONE), EIGHT))
nineDef = integers.stateAxiom(Equals(Add(EIGHT, ONE), NINE))
tenDef = integers.stateAxiom(Equals(Add(NINE, ONE), TEN))
elevenDef = integers.stateAxiom(Equals(Add(TEN, ONE), ELEVEN))
twelveDef = integers.stateAxiom(Equals(Add(ELEVEN, ONE), TWELVE))
thirteenDef = integers.stateAxiom(Equals(Add(TWELVE, ONE), THIRTEEN))
fourteenDef = integers.stateAxiom(Equals(Add(THIRTEEN, ONE), FOURTEEN))
fifteenDef = integers.stateAxiom(Equals(Add(FOURTEEN, ONE), FIFTEEN))
sixteenDef = integers.stateAxiom(Equals(Add(FIFTEEN, ONE), SIXTEEN))

infinityDef = integers.stateAxiom(Forall([(n, INTEGERS)], LessThan(n, INFINITY)))

k = Variable('k')
m = Variable('m')
n = Variable('n')

# ONE in NATURALS
oneInNaturals = integers.stateAxiom(In(ONE, NATURALS))

# forall_{n in NATURALS} (n+1) in NATURALS
successorInNaturals = integers.stateAxiom(Forall([(n, NATURALS)], In(Add(n, ONE)), NATURALS))

# set comprehension S = {x in NATURALS | P(x)}

# forall_{S} [ZERO in S and forall_{n in S} (n+1) in S] => (NATURALS subseteq S)
countingCompletion = integers.stateAxiom(Forall([S], Implies(And(In(ZERO, S), Forall([(n, S)], In(Add(n, ONE), S))), SubsetEq(NATURALS, S))))

# preferable: forall_{P in Map(NATURALS, BOOLS)}
# forall_{P} [P(1) and forall_{n in NATURALS} P(n) => P(n+1)] => [forall_{n in NATURALS} P(n)]
def inductionDerivation():
    # [ONE in {x | P(x)} and forall_{n in {x | P(x)}} (n+1) in {x | P(x)}] => (NATURALS subseteq {x | P(x)})
    countingCompletion.specialize({S:SetOfAll([x], x, suchThat=Px)})

induction = inductionDerivation()










# forall_{m, n} (m - n) = (m + (-n))
subtractDef = integers.stateAxiom(Forall([m, n], Equals(Subtract(m, n), Add(m, Negate(n)))))

# forall_{m in INTEGERS} Range(m, m) = Singleton(m)
singletonRange = integers.stateAxiom(Forall([(m, INTEGERS)], Equals(Range(m, m), Singleton(m))))

# forall_{m in INTEGERS, n in INTEGERS} Range(m, n+1) = [Range(m, n) union Singleton(n+1)]
upperExtendedRange = integers.stateAxiom(Forall([(m, INTEGERS), (n, INTEGERS)], Equals(Range(m, Add(n, ONE)), Union(Range(m, n), Singleton(Add(n, ONE))))))

# Range(m, n) = [Range(m+1, n) union Singleton(m)]
lowerExtendedRange = integers.stateAxiom(Forall([(m, INTEGERS), (n, INTEGERS)], Equals(Range(m, n), Union(Range(Add(m, ONE), n), Singleton(m)))))

# ZERO in INTEGERS
zeroInIntegers = integers.stateAxiom(In(ZERO, INTEGERS))

# INTEGERS = Range(-INFINITY, INFINITY)
inegersDef = integers.stateAxiom(Equals(INTEGERS, Range(Negate(INFINITY), INFINITY)))

# NATURALS = Range(ONE, INFINITY)
naturalsDef = integers.stateAxiom(Equals(NATURALS, Range(ONE, INFINITY)))

# NON_NEGATIVES = ZERO union NATURALS
nonNegativesDef = integers.stateAxiom(Equals(NON_NEGATIVES, Union(ZERO, NATURALS)))


P = Variable('P')
P1 = Operation(P, [ONE])
Pn = Operation(P, [n])
PnPlus1 = Operation(P, [Add(n, ONE)])

# forall_{P} {[P(1) and forall_{n in naturals} P(n) => P(n+1)] => forall_{n in naturals} P(n)}
inductionAxiom = integers.stateAxiom(Forall([P], And(P1, Forall([(n, NATURALS)], Implies(Pn, PnPlus1))), Forall([(n, NATURALS)], Pn)))

def induce(Pn, n):
    '''
    Given P(n) and n, deduce forall_{n in naturals} P(n) from P(1) and forall_{n in naturals} P(n)
    via the inductionAxiom.
    '''
    subMap = SubstitutionMap()
    subMap.substituteOp(P, Pn, n)
    induction = inductionAxiom.specialize(subMap)
    # make sure [P(1) and forall_{n in naturals} P(n) => P(n+1)] derives from both parts being true
    compose(induction.hypothesis.operators[0], induction.hypothesis.operators[1])
    return induction.deriveConclusion()


FIRSTOPERAND = integers.addLiteral('FIRSTOPERAND')
SECONDOPERAND = integers.addLiteral('SECONDOPERAND')

Op = Variable('Op')
A = Variable('A')
B = Variable('B')
n = Variable('n')

class FirstOperand(Operation):
    def __init__(self, operand):
        Operation.__init__(self, FIRSTOPERAND, [operand])

    def remake(self, operator, operands):
        if operator == FIRSTOPERAND and len(operands) == 1:
            return FirstOperand(operands[0])
        else:
            return Operation.remake(self, operator, operands)

class SecondOperand(Operation):
    def __init__(self, operand):
        Operation.__init__(self, SECONDOPERAND, [operand])

    def remake(self, operator, operands):
        if operator == SECONDOPERAND and len(operands) == 1:
            return SecondOperand(operands[0])
        else:
            return Operation.remake(self, operator, operands)


# forall_{Op, A} FirstOperand(Op(A)) = A
firstOpBaseDef = integers.stateAxiom(Forall([Op, A], Equals(FirstOperand(Operation(Op, [A])), A)))
# forall_{Op, A, B} FirstOperand(Op(A, B)) = A
firstOpDef = integers.stateAxiom(Forall([Op, A, B], Equals(FirstOperand(Operation(Op, [A, B])), A)))

# forall_{Op, A, B} SecondOperand(Op(A, B)) = B
secondOpDef = integers.stateAxiom(Forall([Op, A, B], Equals(SecondOperand(Operation(Op, [A, B])), B)))
"""

registerTheorems(__name__, locals())

Context.current = prevContext