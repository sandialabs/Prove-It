import sys
from proveit.expression import Literal, LATEX, STRING, Operation
#from proveit.statement import *
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation, OperationOverInstances
from proveit.everythingLiteral import EVERYTHING
#from variables import *
#from variables import a, b
#import variables as var
from simpleExpr import cEtc
from proveit.number.variables import zero, infinity,a,b,c,A,r,m,k,l, Am

pkg = __package__

class DiscreteContiguousSet(BinaryOperation):
    r'''
    Contiguous set of integers, from lowerBound to upperBound (both bounds to be interpreted inclusively)
    '''
    def __init__(self, lowerBound, upperBound):
        BinaryOperation.__init__(self, DISCRETECONTIGUOUSSET, lowerBound, upperBound)
        self.lowerBound = lowerBound
        self.upperBound = upperBound
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\{'+self.lowerBound.formatted(formatType, fence=fence) +'\ldots '+ self.upperBound.formatted(formatType, fence=fence)+'\}'
        else:
            return r'\{'+self.lowerBound.formatted(formatType, fence=fence) +'...'+ self.upperBound.formatted(formatType, fence=fence)+'\}'

DISCRETECONTIGUOUSSET = Literal(pkg, 'DISCRETECONTIGUOUSSET', operationMaker = lambda operands : DiscreteContiguousSet(*operands))

class Ket(Operation):
    def __init__(self, A):
        Operation.__init__(self, KET, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'|'+self.operand.formatted(formatType, fence=fence)+'\\rangle'
        else:
            return '|'+self.operand.formatted(formatType, fence=fence)+'>'

KET = Literal(pkg, 'KET', operationMaker = lambda operands : Ket(*operands))

class LessThanEquals(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if second number is at least as big as first.
        '''
        BinaryOperation.__init__(self, LESSTHANEQUALS,operandA,operandB)
        
LESSTHANEQUALS = Literal(pkg,'LESSTHANEQUALS', {STRING: r'<=', LATEX:r'\leq'}, operationMaker = lambda operands : LessThanEquals(*operands))

class LessThan(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if second number is at bigger than first.
        '''
        BinaryOperation.__init__(self, LESSTHAN,operandA,operandB)

LESSTHAN = Literal(pkg,'LESSTHAN', {STRING: r'<', LATEX:r'<'}, operationMaker = lambda operands : LessThan(*operands))

class GreaterThanEquals(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if first number is at least as big as second.
        '''
        BinaryOperation.__init__(self, GREATERTHANEQUALS,operandA,operandB)
        
GREATERTHANEQUALS = Literal(pkg,'GREATERTHANEQUALS', {STRING: r'>=', LATEX:r'\geq'}, operationMaker = lambda operands : GreaterThanEquals(*operands))

class GreaterThan(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        See if first number is at least as big as second.
        '''
        BinaryOperation.__init__(self, GREATERTHAN,operandA,operandB)
        
GREATERTHAN = Literal(pkg,'GREATERTHAN', {STRING: r'>', LATEX:r'>'}, operationMaker = lambda operands : GreaterThan(*operands))

class Pr(Operation):
    def __init__(self, A):
        Operation.__init__(self, PR, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        return 'Pr['+self.operand.formatted(formatType, fence=True)+']'

PR = Literal(pkg, 'PR', operationMaker = lambda operands : Pr(*operands))

class Abs(Operation):
    def __init__(self, A):
        Operation.__init__(self, ABS, A)
        self.operand = A

    def formatted(self, formatType, fence=False):

        return '|'+self.operand.formatted(formatType, fence=fence)+'|'

ABS = Literal(pkg, 'ABS', operationMaker = lambda operands : Abs(*operands))

class Add(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        AssociativeOperation.__init__(self, ADD, *operands)
#    def commute(self,index0,index1):
    def commute(self):#Only works at present for two-place addition
        if len(self.operands)!=2:
            raise ValueError('This method can only commute two-place addition.')
        else:
            from proveit.number.theorems import commAdd
            return commAdd.specialize({a:self.operands[0],b:self.operands[1]})


ADD = Literal(pkg, 'ADD', {STRING: r'+', LATEX: r'+'}, operationMaker = lambda operands : Add(*operands))

class Subtract(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Subtract one number from another
        '''
        BinaryOperation.__init__(self, SUBTRACT, operandA, operandB)

SUBTRACT = Literal(pkg, 'SUBTRACT', {STRING: r'-', LATEX: r'-'}, operationMaker = lambda operands : Subtract(*operands))

class Multiply(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        AssociativeOperation.__init__(self, MULTIPLY, *operands)

MULTIPLY = Literal(pkg, 'MULTIPLY', {STRING: r'*', LATEX: r'\cdot'}, operationMaker = lambda operands : Multiply(*operands))

class Divide(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        BinaryOperation.__init__(self, DIVIDE, operandA, operandB)

DIVIDE = Literal(pkg, 'DIVIDE', {STRING: r'/', LATEX: r'\div'}, operationMaker = lambda operands : Divide(*operands))

class Fraction(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands in fraction form.
        '''
        BinaryOperation.__init__(self, FRACTION, operandA, operandB)
        self.numerator = operandA
        self.denominator = operandB

    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\frac{'+self.numerator.formatted(formatType, fence=fence)+'}{'+ self.denominator.formatted(formatType, fence=fence)+'}'
        elif formatType == STRING:
            return Divide(self.numerator, self.denominator).formatted(STRING)
        else:
            print "BAD FORMAT TYPE"
            return None

FRACTION = Literal(pkg, 'FRACTION', operationMaker = lambda operands : Fraction(*operands))

class Exponentiate(BinaryOperation):
    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        BinaryOperation.__init__(self,EXPONENTIATE, base, exponent)
        self.base = base
        self.exponent = exponent
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return self.base.formatted(formatType, fence=fence)+'^{'+self.exponent.formatted(formatType, fence=fence)+'}'
        elif formatType == STRING:
            return self.base.formatted(formatType, fence=fence)+'^('+self.exponent.formatted(formatType, fence=fence)+')'
        else:
            print "BAD FORMAT TYPE"
            return None

EXPONENTIATE = Literal(pkg, 'EXPONENTIATE', operationMaker = lambda operands : Exponentiate(*operands))

#def extractExpBase(exponentiateInstance):
#    if not isinstance(exponentiateInstance,Exponentiate):
#        raise ValueError("ExponentiateInstances is not an instance of exponentiate!")
#    else:
#        return exponentiateInstance.base

class Summation(OperationOverInstances):
#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
#    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, indices, summand, domain, conditions = tuple()):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        indices: instance vars
        summand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(self, SUMMATION, indices, summand, domain=domain, conditions=conditions)
        self.indices = self.instanceVars
        self.summand = self.instanceExpr
#        self.domain = domain#self.domain already set

    def reduceGeomSum(self):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        '''
        from proveit.number.theorems import infGeomSum, finGeomSum
        self.m = self.indices[0]
        
        try:
#            self.r = extractExpBase(self.summand)
            self.r = self.summand.base
        except:
            raise ValueError("Summand not an exponential!")
        if not isinstance(self.domain,DiscreteContiguousSet):
            raise ValueError("Not explicitly summing over DiscreteContiguousSet!")
        else:
            if self.domain.lowerBound == zero and self.domain.upperBound == infinity:
                #We're in the infinite geom sum domain!
                return infGeomSum.specialize({r: self.r, m:self.m})
            else:
                #We're in the finite geom sum domain!
                self.k = self.domain.lowerBound
                self.l = self.domain.upperBound
                return finGeomSum.specialize({r:self.r, m:self.m, k:self.k, l:self.l})
#        else:
#            print "Not a geometric sum!"
    def splitSumApart(self,splitIndex):
    #Something is not right here- e.g.:
#        zz = Summation(x,Bm,DiscreteContiguousSet(k,l))
#        zz.splitSumApart(t)
##       replaces B(m) with B(x), which is... not right.
        r'''
        Splits sum over one DiscreteContiguousSet into sum over two, splitting at splitIndex. 
        r'''
        from proveit.number.theorems import splitSum
        self.m = self.indices[0]
        self.a = self.domain.lowerBound
        self.c = self.domain.upperBound
        self.b = splitIndex
        self.Aselfm = Operation(A,self.m)
        return splitSum.specialize({m:self.m,a:self.a,b:self.b,c:self.c,self.Aselfm:self.summand})


def summationMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return Summation(params['instanceVars'],params['instanceExpr'],params['domain'],params['conditions'])

    
#SUMMATION = Literal(pkg, "SUMMATION", {STRING: r'Summation', LATEX: r'\sum'}, operationMaker = lambda operands : Summation(*OperationOverInstances.extractParameters(operands)))

SUMMATION = Literal(pkg, "SUMMATION", {STRING: r'Summation', LATEX: r'\sum'}, operationMaker = summationMaker)
'''
class Abs(Operation):
    def __init__(self, A):
        Operation.__init__(self, ABS, A)
        self.operand = A

    def formatted(self, formatType, fence=False):

        return '|'+self.operand.formatted(formatType, fence=fence)+'|'

ABS = Literal(pkg, 'ABS', operationMaker = lambda operands : Abs(*operands))
'''
class Neg(Operation):
    def __init__(self,A):
        Operation.__init__(self, NEG, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        return '-'+self.operand.formatted(formatType, fence=fence)
        
NEG = Literal(pkg, 'NEG', operationMaker = lambda operands : Neg(*operands))