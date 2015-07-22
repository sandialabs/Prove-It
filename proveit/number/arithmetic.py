import sys
from proveit.statement import *
from proveit.context import Context
from proveit.basiclogic.genericOperations import AssociativeOperation, BinaryOperation, OperationOverInstances
#from variables import *
from variables import a, b, cStar

literals = Literals()
DISCRETECONTIGUOUSSET = literals.add('DISCRETECONTIGUOUSSET')
KET = literals.add('KET')
LESSTHANEQUALS = literals.add('LESSTHANEQUALS')#Add to a different script in numbers?
LESSTHAN = literals.add('LESSTHAN')#Add to a different script in numbers?
GREATERTHANEQUALS = literals.add('GREATERTHANEQUALS')#Add to a different script in numbers?
GREATERTHAN = literals.add('GREATERTHAN')#Add to a different script in numbers?
PR = literals.add('PR')#Add to a different script in numbers?
ABS = literals.add('ABS')#Add to a different script in numbers?
ADD = literals.add('ADD')
SUBTRACT = literals.add('SUBTRACT')
MULTIPLY = literals.add('MULTIPY')
DIVIDE = literals.add('DIVIDE')
FRACTION = literals.add('FRACTION')
EXPONENTIATE = literals.add('EXPONENTIATE')
SUMMATION = literals.add('SUMMATION')
PRODUCT = literals.add('PRODUCT')


m = Variable('m')
n = Variable('n')
t = Variable('t')
eps = Variable('eps',{LATEX:r'\varepsilon'})
#e = Variable('e')
phi = Variable('phi',{LATEX:r'\phi'})

#U   = Variable('U')
U   = literals.add('U')
#SUm = Variable('SU(m)')
SUm = Operation(U,m)
C2m = Variable('C^(2^m)',{LATEX:r'C^{2^m}'})

H = literals.add('H',{LATEX:r'\mathcal{H}'})
Hm = Operation(H,m)

u = Variable('ket_u',{LATEX:r'|u\rangle'})

e = literals.add('e')
i = literals.add('i')
pi = Variable('pi',{LATEX:r'\pi'})

k = Variable('k')
l = Variable('l')

zero = literals.add('0')
one = literals.add('1')
two = literals.add('2')
infinity = literals.add('infinity',{LATEX:r'\infty'})
minusOne = literals.add('minusOne',{LATEX:r'-1'})
minusTwo = literals.add('minusTwo',{LATEX:r'-2'})

Z   = literals.add('Z',{LATEX:r'\mathbb{Z}'})
Zp  = literals.add('Z^+',{LATEX:r'\mathbb{Z}^+'})
R   = literals.add('R',{LATEX:r'\mathbb{R}'})
zeroToOne = literals.add('zeroToOne',{LATEX:r'[0,1]'})

tFunc = literals.add('tFunc')
tFunc_n_eps = Operation(tFunc, (n, eps))

QPE = literals.add('QPE')
QPEfunc = Operation(QPE,(U,u,t))



#ZPLUS = literal.add('ZPLUS')

#QPE should be literal
#Can't have unbound variables.


def _defineAxioms():  
    # Composition of multi-Add, bypassing associativity for notational convenience:
    # forall_{a, b, c**} a + b + c** = a + (b + c**)
    _firstAxiom =\
    addComposition = Forall((a, b, cStar), Equals(Add(a, b, cStar), Add(a, Add(b, cStar))))
  
    return _firstAxiom, locals()

def _defineTheorems():
#    from equality import Equals, NotEquals
    
    # Not(FALSE)
#    _firstTheorem =\
#    notFalse = Not(FALSE)

    infGeomSum = Forall(r,Equals(Summation(r,Exponentiate(r,m),In(r,DiscreteContiguousSet(zero,infinity))), 
             Fraction(one,Subtract(one,r))),
              In(r,R),
              )
    finGeomSum = Forall([r,m,n],Equals(Summation(r,Exponentiate(r,m),In(r,DiscreteContiguousSet(m,n))), 
             Fraction(Subtract(Exponentiate(r,Add(n,one)),Exponentiate(r,m)),Subtract(r,one))),
             [In(m,Z),
              In(n,Z),
              In(r,R),
              LessThan(m,n)])
    return locals()

arithmetic = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)

class DiscreteContiguousSet(BinaryOperation):
    def __init__(self, lowerBound, upperBound):
        BinaryOperation.__init__(self, DISCRETECONTIGUOUSSET, lowerBound, upperBound)
        self.lowerBound = lowerBound
        self.upperBound = upperBound
    
    def formatted(self, formatType, fenced=False):
        if formatType == LATEX:
            return r'\{'+self.lowerBound.formatted(formatType, fenced=True) +'\ldots '+ self.upperBound.formatted(formatType, fenced=True)+'\}'
        else:
            return r'\{'+self.lowerBound.formatted(formatType, fenced=True) +'...'+ self.upperBound.formatted(formatType, fenced=True)+'\}'

class Ket(Operation):
    def __init__(self, A):
        Operation.__init__(self, PR, A)
        self.operand = A
    
    def formatted(self, formatType, fenced=False):
        if formatType == LATEX:
            return r'|'+self.operand.formatted(formatType, fenced=True)+'\\rangle'
        else:
            return '|'+self.operand.formatted(formatType, fenced=True)+'>'

class LessThanEquals(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if second number is at least as big as first.
        '''
        BinaryOperation.__init__(self, LESSTHANEQUALS,operandA,operandB)
        
    def formattedOperator(self, formatType):
        '''
        Formated operator when there are 2 or operands (can't be more).
        '''
        if formatType == STRING:
            return r'<='
        elif formatType == LATEX:
            return r'\leq'

class LessThan(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if second number is at bigger than first.
        '''
        BinaryOperation.__init__(self, LESSTHANEQUALS,operandA,operandB)
        
    def formattedOperator(self, formatType):
        '''
        Formated operator when there are 2 or operands (can't be more).
        '''
        if formatType == STRING:
            return r'<'
        elif formatType == LATEX:
            return r'<'

class GreaterThanEquals(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if first number is at least as big as second.
        '''
        BinaryOperation.__init__(self, GREATERTHANEQUALS,operandA,operandB)
        
    def formattedOperator(self, formatType):
        '''
        Formated operator when there are 2 or operands (can't be more).
        '''
        if formatType == STRING:
            return r'>='
        elif formatType == LATEX:
            return r'\geq'

class GreaterThan(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if first number is bigger than second.
        '''
        BinaryOperation.__init__(self, LESSTHANEQUALS,operandA,operandB)
        
    def formattedOperator(self, formatType):
        '''
        Formated operator when there are 2 or operands (can't be more).
        '''
        if formatType == STRING:
            return r'<'
        elif formatType == LATEX:
            return r'<'


class Pr(Operation):
    def __init__(self, A):
        Operation.__init__(self, PR, A)
        self.operand = A
    
    def formatted(self, formatType, fenced=False):
        return 'Pr['+self.operand.formatted(formatType, fenced=True)+']'

class Abs(Operation):
    def __init__(self, A):
        Operation.__init__(self, ABS, A)
        self.operand = A

    def formatted(self, formatType, fenced=False):

        return '|'+self.operand.formatted(formatType, fenced=True)+'|'

class Add(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        AssociativeOperation.__init__(self, ADD, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        return '+'
        
class Subtract(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Subtract one number from another
        '''
        BinaryOperation.__init__(self, SUBTRACT, operandA, operandB)
        
    def formattedOperator(self, formatType):
        '''
        Formated operator when there are 2 or operands (can't be more).
        '''
        return '-'

class Multiply(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        AssociativeOperation.__init__(self, MULTIPLY, *operands)

    def formattedOperator(self, formatType):
        r'''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return r'*'
        elif formatType == LATEX:
            return r'\cdot'

class Divide(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        BinaryOperation.__init__(self, DIVIDE, operandA, operandB)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
             return r'/'
        elif formatType == LATEX:
             return r'\div'

class Fraction(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands in fraction form.
        '''
        BinaryOperation.__init__(self, FRACTION, operandA, operandB)
        self.numerator = operandA
        self.denominator = operandB

    def formatted(self, formatType, fenced=False):
        return r'\frac{'+self.numerator.formatted(formatType, fenced=True)+'}{'+ self.denominator.formatted(formatType, fenced=True)+'}'


#    def formatted(self, formatType, fenced=False, subLeftFenced=True, subRightFenced=True):#What does fenced mean?
#        # override this default as desired
#        r'''
#        Formatted operator when there are 2 or more operands.
#        '''
##        if format
#        pass

class Exponentiate(BinaryOperation):
    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        BinaryOperation.__init__(self,EXPONENTIATE, base, exponent)
        self.base = base
        self.exponent = exponent
    
    def formatted(self, formatType, fenced=False):
        return self.base.formatted(formatType, fenced=True)+'^{'+self.exponent.formatted(formatType, fenced=True)+'}'

#    def formattedOperator(self, formatType):
#        if formatType == STRING:
#            return r'**'
#        elif formatType == LATEX:
#            return r'^'

class Summation(OperationOverInstances):
#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
    def __init__(self, indices, summand, domains):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        indices: instance vars
        summand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(self, SUMMATION, indices, summand, domains)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'Summation'
        elif formatType == LATEX:
            return '\sum'
