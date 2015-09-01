import sys
from proveit.expression import Literal, LATEX, STRING, Operation, Variable, safeDummyVar
from proveit.multiExpression import Etcetera
from proveit.basiclogic import Equals, Equation
#from proveit.number import axioms
#from proveit.statement import *
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation, OperationOverInstances
from proveit.everythingLiteral import EVERYTHING
from proveit.common import a, b, c, m, k, l, r, v, w, x, y, z, A
#from variables import *
#from variables import a, b
#import variables as var
#from simpleExpr import cEtc
#from proveit.number.variables import zero, one, infinity,a,b,c,A,r,m,k,l,x,y,z, Am, Reals, Integers, Naturals
#from proveit.number.common import *

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

class Interval(BinaryOperation):
    r'''
    Base class for all permutations of closed and open intervals.  
    Do not construct an object of this class directly!  Instead, use IntervalOO or IntervalOC etc.
    '''
    def __init__(self,operator,lowerBound,upperBound):
        BinaryOperation.__init__(self,operator,lowerBound,upperBound)
        self.lowerBound = lowerBound
        self.upperBound = upperBound
        
class IntervalOO(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALOO,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right)'
        else:
            return r'('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r')'

INTERVALOO = Literal(pkg, 'INTERVALOO', operationMaker = lambda operands : IntervalOO(*operands))


class IntervalOC(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALOC,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right]'
        else:
            return r'('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r']'

INTERVALOC = Literal(pkg, 'INTERVALOC', operationMaker = lambda operands : IntervalOC(*operands))

class IntervalCO(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALCO,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right)'
        else:
            return r'['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r')'

INTERVALCO = Literal(pkg, 'INTERVALCO', operationMaker = lambda operands : IntervalCO(*operands))

class IntervalCC(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALCC,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right]'
        else:
            return r'['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r']'

INTERVALCC = Literal(pkg, 'INTERVALCC', operationMaker = lambda operands : IntervalCC(*operands))

class OrderingRelation(BinaryOperation):
    r'''
    Base class for all strict and non-strict inequalities.
    Do not construct an object of this class directly!  Instead, use LessThan, LessThanEquals etc.
    '''
    def __init__(self, operator,lhs, rhs):
        BinaryOperation.__init__(self,operator, lhs, rhs)
        self.operator = operator
        self.lhs = lhs
        self.rhs = rhs

    def deriveReversed(self):
        '''
        From, e.g., x >= y derive y <= x etc.
        '''
        from proveit.number.axioms import reverseGreaterThanEquals, reverseLessThanEquals, reverseGreaterThan, reverseLessThan
        if self.operator == LESSTHANEQUALS:
            return reverseLessThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == LESSTHAN:
            return reverseLessThan.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == GREATERTHANEQUALS:
            return reverseGreaterThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == GREATERTHAN:
            return reverseGreaterThan.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        else:
            raise ValueError("Invalid instance of OrderingRelation!")
    def applyTransitivity(self, other):
        if isinstance(other,Equals):
            if other.lhs in (self.lhs, self.rhs):
                subrule = other.rhsSubstitute
                commonExpr = other.lhs
            elif other.rhs in (self.lhs, self.rhs):
                subrule = other.lhsSubstitute
                commonExpr = other.rhs
            else:
                raise ValueError("Equality does not involve either side of inequality!")
            X = safeDummyVar(self)
            if commonExpr == self.lhs:
                return subrule(self.operator.operationMaker([X,self.rhs]),X)
            elif commonExpr == self.rhs:
                return subrule(self.operator.operationMaker([self.lhs,X]),X)
#                    return other.rhsSubstitute(X,self.operator.operationMaker([X,self.rhs]))
#                else:
#                    return other.rhsSubstitute(X,
        return self.transitivityImpl(other).deriveConclusion().checked({self, other})

class LessThan(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at bigger than first.
        '''
        OrderingRelation.__init__(self, LESSTHAN,lhs,rhs)
    def transitivityImpl(self,other):
        from proveit.number.axioms import reverseGreaterThanEquals, reverseGreaterThan
        from proveit.number.axioms import lessThanTransLessThanRight, lessThanTransLessThanEqualsRight
        from proveit.number.axioms import lessThanTransLessThanLeft, lessThanTransLessThanEqualsLeft

                

        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed()
#            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                print self,result
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
        else:
            raise ValueError("Cannot derive implication from input!")


LESSTHAN = Literal(pkg,'LESSTHAN', {STRING: r'<', LATEX:r'<'}, operationMaker = lambda operands : LessThan(*operands))

class LessThanEquals(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at least as big as first.
        '''
        OrderingRelation.__init__(self, LESSTHANEQUALS,lhs,rhs)
    def transitivityImpl(self,other):
        from proveit.number.axioms import reverseGreaterThanEquals, reverseGreaterThan
        from proveit.number.axioms import lessThanEqualsTransLessThanRight, lessThanEqualsTransLessThanEqualsRight
        from proveit.number.axioms import lessThanEqualsTransLessThanLeft, lessThanEqualsTransLessThanEqualsLeft
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed()
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
 #           result = equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}).deriveConclusion()
        else:
            raise ValueError("Cannot derive implication from input!")
        
LESSTHANEQUALS = Literal(pkg,'LESSTHANEQUALS', {STRING: r'<=', LATEX:r'\leq'}, operationMaker = lambda operands : LessThanEquals(*operands))


class GreaterThan(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, GREATERTHAN,lhs,rhs)
    def transitivityImpl(self,other):
        from proveit.number.axioms import reverseLessThanEquals, reverseLessThan
        from proveit.number.axioms import greaterThanTransGreaterThanRight, greaterThanTransGreaterThanEqualsRight
        from proveit.number.axioms import greaterThanTransGreaterThanLeft, greaterThanTransGreaterThanEqualsLeft
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,LessThan) or isinstance(other,LessThanEquals):
            other = other.deriveReversed()
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.
        if other.lhs == self.rhs:
            if isinstance(other,GreaterThan):
                result = greaterThanTransGreaterThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result.checked({self})
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanTransGreaterThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,GreaterThan):
                result = greaterThanTransGreaterThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanTransGreaterThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
        else:
            raise ValueError("Cannot derive implication from input!")

GREATERTHAN = Literal(pkg,'GREATERTHAN', {STRING: r'>', LATEX:r'>'}, operationMaker = lambda operands : GreaterThan(*operands))

class GreaterThanEquals(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, GREATERTHANEQUALS,lhs,rhs)
    def transitivityImpl(self,other):
        from proveit.number.axioms import reverseLessThanEquals, reverseLessThan
        from proveit.number.axioms import greaterThanEqualsTransGreaterThanRight, greaterThanEqualsTransGreaterThanEqualsRight
        from proveit.number.axioms import greaterThanEqualsTransGreaterThanLeft, greaterThanEqualsTransGreaterThanEqualsLeft
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,LessThan) or isinstance(other,LessThanEquals):
            other = other.deriveReversed()
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.
        if other.lhs == self.rhs:
            if isinstance(other,GreaterThan):
                result = greaterThanEqualsTransGreaterThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result.checked({self})
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanEqualsTransGreaterThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,GreaterThan):
                result = greaterThanEqualsTransGreaterThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanEqualsTransGreaterThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
        else:
            raise ValueError("Cannot derive implication from input!")

GREATERTHANEQUALS = Literal(pkg,'GREATERTHANEQUALS', {STRING: r'>=', LATEX:r'\geq'}, operationMaker = lambda operands : GreaterThanEquals(*operands))

class Abs(Operation):
    def __init__(self, A):
        Operation.__init__(self, ABS, A)
        self.operand = A

    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return '|'+self.operand.formatted(formatType, fence=fence)+'|'
        elif formatType == LATEX:
            return r'\left|'+self.operand.formatted(formatType, fence=fence)+r'\right|'
        

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
    def factor(self,operand,pull="left"):
        from proveit.number.complex.theorems import multComm, multAssoc
        if operand not in self.operands:
            raise ValueError("Trying to factor out absent expression!")
        elif len(self.operands) == 2 :
            if (pull == 'left' and self.operands[0] == operand) or (pull == 'right' and self.operands[1] == operand):
                from proveit.basiclogic.equality.axioms import equalsReflexivity
                return equalsReflexivity.specialize({x:self}).checked()
            else:
                return multComm.specialize(
                {Etcetera(v):[],Etcetera(w):self.operands[0],Etcetera(x):[],Etcetera(y):self.operands[1],Etcetera(z):[]}
                ).checked()
        else:
            splitIndex = self.operands.index(operand)
            newOperandsLeft = self.operands[:splitIndex]
            newOperandsRight = self.operands[splitIndex+1:]
            newOperands = newOperandsLeft + newOperandsRight
#                
            if pull == "left":
                intermediate1 = multComm.specialize(
                    {Etcetera(v):[],Etcetera(w):[],Etcetera(x):newOperandsLeft,Etcetera(y):operand,Etcetera(z):newOperandsRight}
                                            )#.deriveRightViaEquivalence()
                intermediate2 = multAssoc.specialize(
                    {Etcetera(w):operand,Etcetera(x):newOperands,Etcetera(y):[],Etcetera(z):[]})#.deriveRightViaEquivalence()
                eq = Equation(intermediate1)
                eq.update(intermediate2)
                return eq.eqExpr.checked()
            elif pull == "right":
                intermediate1 = multComm.specialize(
                    {Etcetera(v):newOperandsLeft,Etcetera(w):operand,Etcetera(x):[],Etcetera(y):newOperandsRight,Etcetera(z):[]}
                                            )
                intermediate2 = multAssoc.specialize(
                    {Etcetera(w):[],Etcetera(x):newOperands,Etcetera(y):[],Etcetera(z):operand})
                eq = Equation(intermediate1)
                eq.update(intermediate2)
                return eq.eqExpr.checked()
            else:
                raise ValueError("Invalid pull arg. provided!  (Acceptable values are \"left\" and \"right\".)")

        AssociativeOperation.__init__(self, MULTIPLY, *operands)
    def factorRhs(self,operand,pull="left"):
        return self.factor(operand,pull=pull).deriveRightViaEquivalence()


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
        from proveit.number.common import Reals, Integers, Naturals, zero, infinity
        OperationOverInstances.__init__(self, SUMMATION, indices, summand, domain=domain, conditions=conditions)
        if len(self.instanceVars) != 1:
            raise ValueError('Only one index allowed per integral!')
        
        self.indices = self.instanceVars
        self.summand = self.instanceExpr
        self.index = self.instanceVars[0]
        if isinstance(self.domain,Interval):
            raise ValueError('Summation cannot sum over non-discrete set (e.g. Interval)')
        elif self.domain == Reals:
            raise ValueError('Summation cannot sum over Reals.')
        elif self.domain == Integers:
            self.domain = DiscreteContiguousSet(Neg(infinity),infinity)
        elif self.domain == Naturals:
            self.domain = DiscreteContiguousSet(zero,infinity)
        
        
#        self.domain = domain#self.domain already set

    def formatted(self, formatType, fence=False):

        if isinstance(self.domain,DiscreteContiguousSet):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            return self.operator.formatted(formatType)+r'_{'+self.index.formatted(formatType)+'='+lower+r'}'+r'^{'+upper+r'}'+self.summand.formatted(formatType, fence=fence)
        else:
            return self.operator.formatted(formatType)+r'_{'+self.index.formatted(formatType)+r'\in '+self.domain.formatted(formatType)+r'}'+self.summand.formatted(formatType, fence=fence)



    def reduceGeomSum(self):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        '''
        from proveit.number.theorems import infGeomSum, finGeomSum
        from proveit.number.common import zero, infinity
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

class Neg(Operation):
    def __init__(self,A):
        Operation.__init__(self, NEG, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        return '-'+self.operand.formatted(formatType, fence=True)
        
NEG = Literal(pkg, 'NEG', operationMaker = lambda operands : Neg(*operands))

class Integrate(OperationOverInstances):
#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
#    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, index, integrand, domain, conditions = tuple()):
        r'''
        Integrates integrand over indices over domain.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        index: single instance var
        integrand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        from proveit.number.common import Reals, infinity
        OperationOverInstances.__init__(self, INTEGRATE, index, integrand, domain=domain, conditions=conditions)
        self.domain = domain
        if len(self.instanceVars) != 1:
            raise ValueError('Only one index allowed per integral!')
        elif isinstance(self.domain,DiscreteContiguousSet):
            raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        elif self.domain == Reals:
            self.domain = IntervalCC(Neg(infinity),infinity)
        elif not isinstance(self.domain,IntervalCC):
#            if not isinstance(self.domain,IntervalCC):
            raise ValueError("domain must be IntervalCC or Reals!")
        self.index = self.instanceVars[0]
        self.integrand = self.instanceExpr
        
    def formatted(self, formatType, fence=False):
#        if isinstance(self.domain,IntervalOO) or isinstance(self.domain,IntervalOC) or isinstance(self.domain,IntervalCO) or isinstance(self.domain,IntervalOO):
        if isinstance(self.domain,Interval):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            return self.operator.formatted(formatType)+r'_{'+lower+r'}'+r'^{'+upper+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)
#        elif self.domain

        return self.operator.formatted(formatType)+r'_{'+self.domain.formatted(formatType)+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)


def integrateMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return Integrate(params['instanceVars'],params['instanceExpr'],params['domain'],params['conditions'])


INTEGRATE = Literal(pkg, "INTEGRATE", {STRING: r'Integrate', LATEX: r'\int'}, operationMaker = integrateMaker)
