import sys
from proveit.expression import Literal, LATEX, STRING, Operation, Variable, safeDummyVar
from proveit.multiExpression import Etcetera
from proveit.basiclogic import Equals, Equation, Forall, In
#from proveit.number import axioms
#from proveit.statement import *
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation, OperationOverInstances
from proveit.everythingLiteral import EVERYTHING
from proveit.common import a, b, c, d, k, l, m, n, r, v, w, x, y, z, A, P, S, vEtc, wEtc, xEtc, yEtc, zEtc
from proveit.number.numberSets import *
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

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from integer.theorems import allInDiscreteInterval_InInts
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InInts.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

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

class Abs(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, ABS, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import complex.theorems
        if numberSet == Reals:
            return complex.theorems.absClosure
        elif numberSet == RealsPos:
            return complex.theorems.absPosClosure            

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.absNotEqZero
    
    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return '|'+self.operand.formatted(formatType, fence=fence)+'|'
        elif formatType == LATEX:
            return r'\left|'+self.operand.formatted(formatType, fence=fence)+r'\right|'
        

ABS = Literal(pkg, 'ABS', operationMaker = lambda operands : Abs(*operands))

class Add(AssociativeOperation, NumberOp):
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        AssociativeOperation.__init__(self, ADD, *operands)

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import real.theorems
        import integer.theorems
        if numberSet == Reals:
            return real.theorems.addClosure
        elif numberSet == Complexes:
            return complex.theorems.addClosure
        elif numberSet == Integers:
            return integer.theorems.addClosure
            
#    def commute(self,index0,index1):
    def commute(self, assumptions=frozenset()):#Only works at present for two-place addition
        if len(self.operands)!=2:
            raise ValueError('This method can only commute two-place addition.')
        else:
            from proveit.number.theorems import commAdd
            deduceInComplexes([self.operands[0], self.operands[1]], assumptions)
            return commAdd.specialize({a:self.operands[0],b:self.operands[1]})
    
    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-sum wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from proveit.number.complex.theorems import addAssoc
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:startIdx] if startIdx is not None else []
        ySub = self.operands[startIdx:endIdx]
        zSub = self.operands[endIdx:] if endIdx is not None else []
        return addAssoc.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def ungroup(self, idx, assumptions=frozenset()):
        '''
        Ungroup (un-associate a sub-sum wrapped in parenthesis)
        an operand, self.operands[idx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        if not isinstance(self.operands[idx], Add):  
            raise ValueError("Selected term is not an Add expression")

        from proveit.number.complex.theorems import addAssocRev
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return addAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

ADD = Literal(pkg, 'ADD', {STRING: r'+', LATEX: r'+'}, operationMaker = lambda operands : Add(*operands))

class Subtract(BinaryOperation, NumberOp):
    def __init__(self, operandA, operandB):
        r'''
        Subtract one number from another
        '''
        BinaryOperation.__init__(self, SUBTRACT, operandA, operandB)

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import real.theorems
        if numberSet == Reals:
            return real.theorems.subtractClosure
        elif numberSet == Complexes:
            return complex.theorems.subtractClosure
    
    def factor(self, theFactor, pull='left', groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a common factor from a subtraction, pulling it either to the "left" or "right".
        If there are multiple occurrences in any term, the first occurrence is used.  
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from complex.theorems import distributeThroughSubtractRev
        dummyVar = self.safeDummyVar()
        eq = Equation()
        # commute both terms so that the factor is at the beginning
        factorEqLeft = self.operands[0].factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
        factorEqRight = self.operands[1].factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
        # substitute the factored terms
        eq.update(factorEqLeft.substitution(Subtract(dummyVar, self.operands[1]), dummyVar)).checked(assumptions)
        eq.update(factorEqRight.substitution(Subtract(factorEqLeft.rhs, dummyVar), dummyVar)).checked(assumptions)
        # perform distribution in reverse
        num = len(theFactor.operands) if isinstance(theFactor, Multiply) else 1
        if pull == 'left':
            wEtcSub = theFactor.operands if isinstance(theFactor, Multiply) else [theFactor]
            xSub = factorEqLeft.rhs.operands[num:]
            ySub = factorEqRight.rhs.operands[num:]
            zEtcSub = []
        elif pull == 'right':            
            wEtcSub = []
            xSub = factorEqLeft.rhs.operands[:-num]
            ySub = factorEqRight.rhs.operands[:-num]
            zEtcSub = theFactor.operands if isinstance(theFactor, Multiply) else [theFactor]
        xSub = xSub[0] if len(xSub) == 1 else Multiply(*xSub)
        ySub = ySub[0] if len(ySub) == 1 else Multiply(*ySub)
        deduceInComplexes(wEtcSub + [xSub] + [ySub] + zEtcSub, assumptions)
        eq.update(distributeThroughSubtractRev.specialize({wEtc:wEtcSub, x:xSub, y:ySub, zEtc:zEtcSub}))
        if groupFactor and num > 1:
            if pull=='left':
                eq.update(eq.eqExpr.rhs.group(endIdx=num, assumptions=assumptions))
            elif pull=='right':
                eq.update(eq.eqExpr.rhs.group(startIdx=-num, assumptions=assumptions))                
        return eq.eqExpr.checked(assumptions)

    def cancel(self, idxInFirstSum=None, assumptions=frozenset()):
        from complex.theorems import subtractCancelTwoSums, subtractCancelLeftSum, subtractCancelRightSum
        deduceInComplexes(self.operands[0].operands, assumptions=assumptions)
        deduceInComplexes(self.operands[1].operands, assumptions=assumptions)
        if isinstance(self.operands[0], Add):
            if isinstance(self.operands[1], Add):
                if idxInFirstSum is None:
                    raise Exception("Must supply idxInFirstSum when canceling terms of a subtraction between sums")
                idx1 = idxInFirstSum
                wSub = self.operands[0].operands[idx1]
                try:
                    idx2 = self.operands[1].operands.index(wSub)
                except:
                    raise Exception(str(wSub) + " not found in " + str(self.operands[1]) + " for a subtraction cancel")
                vSub = self.operands[0].operands[:idx1]
                xSub = self.operands[0].operands[idx1+1:]
                ySub = self.operands[1].operands[:idx2]
                zSub = self.operands[1].operands[idx2+1:]
                return subtractCancelTwoSums.specialize({vEtc:vSub, w:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)
            else:
                ySub = self.operands[1]
                try:
                    idx1 = self.operands[0].operands.index(ySub)
                except:
                    raise Exception(str(ySub) + " not found in " + str(self.operands[0]) + " for a subtraction cancel")                    
                if idxInFirstSum is not None and idx1 != idxInFirstSum:
                    raise Exception("idxInFirstSum not consistent with found index (it also isn't necessary when there is only one Add operand of the Subtract)")
                xSub = self.operands[0].operands[:idx1]
                zSub = self.operands[0].operands[idx1+1:]
                return subtractCancelLeftSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions)
        else:
            ySub = self.operands[0]
            try:
                idx2 = self.operands[1].operands.index(ySub)
            except:
                raise Exception(str(ySub) + " not found in " + str(self.operands[1]) + " for a subtraction cancel")                    
            if idxInFirstSum is not None and idx2 != idxInFirstSum:
                raise Exception("idxInFirstSum not consistent with found index (it also isn't necessary when there is only one Add operand of the Subtract)")
            xSub = self.operands[1].operands[:idx2]
            zSub = self.operands[1].operands[idx2+1:]
            return subtractCancelRightSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions)            

SUBTRACT = Literal(pkg, 'SUBTRACT', {STRING: r'-', LATEX: r'-'}, operationMaker = lambda operands : Subtract(*operands))

class Multiply(AssociativeOperation, NumberOp):
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        AssociativeOperation.__init__(self, MULTIPLY, *operands)

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import real.theorems
        if numberSet == Reals:
            return real.theorems.multClosure
        elif numberSet == RealsPos:
            return real.theorems.multPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.multClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.multNotEqZero
    
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from proveit.number.complex.theorems import multComm
        if startIdx1 is None and endIdx1 is None and startIdx2 is None and endIdx2 is None:
            stattIdx1, endIdx1, startIdx2, endIdx2 = 0, 1, 1, None
        nOperands = len(self.operands)
        start1, stop1, _ = slice(startIdx1, endIdx1).indices(nOperands)
        start2, stop2, _ = slice(startIdx2, endIdx2).indices(nOperands)
        if start1  > start2:
            # swap 1 and 2 so that 1 comes first
            startIdx1, endIdx1, startIdx2, endIdx2 = startIdx2, endIdx2, startIdx1, endIdx2
            start1, stop1, start2, stop2 = start2, stop2, start1, stop1
        if stop1 > start2:
            raise ValueError("Cannot commute verlapping sets of operands")
        vSub = self.operands[:startIdx1] if startIdx1 is not None else []
        wSub = self.operands[startIdx1:endIdx1]
        xSub = self.operands[endIdx1:startIdx2]
        ySub = self.operands[startIdx2:endIdx2]
        zSub = self.operands[endIdx2:] if endIdx2 is not None else []
        deduceInComplexes(self.operands, assumptions)
        return multComm.specialize({vEtc:vSub, wEtc:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-product wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from proveit.number.complex.theorems import multAssoc
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:startIdx] if startIdx is not None else []
        ySub = self.operands[startIdx:endIdx]
        zSub = self.operands[endIdx:] if endIdx is not None else []
        return multAssoc.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def ungroup(self, idx, assumptions=frozenset()):
        '''
        Ungroup (un-associate a sub-product wrapped in parenthesis)
        an operand, self.operands[idx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        if not isinstance(self.operands[idx], Multiply):  
            raise ValueError("Selected term is not a Multiply expression")

        from proveit.number.complex.theorems import multAssocRev
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return multAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)
    
    def index(self, theFactor, alsoReturnNum=False):
        '''
        Return the starting index of theFactor, which may be a single operand,
        a list of consecutive operands, or a Multiply expression that represents
        the product of the list of consecutive operands.  If alsoReturnNum is
        True, return a tuple of the index and number of operands for theFactor.
        '''
        if isinstance(theFactor, Multiply):
            theFactor = theFactor.operands
        if hasattr(theFactor, '__getitem__') and hasattr(theFactor, '__len__'):
            # multiple operands in theFactor
            firstFactor = theFactor[0]
            num = len(theFactor)
            idx = -1
            try:
                while True:
                    idx = self.operands.index(firstFactor, idx+1)
                    if tuple(self.operands[idx:idx+num]) == tuple(theFactor):
                        break # found it all!
            except ValueError:
                raise ValueError("Factor is absent!")
        else:
            num = 1
            try:
                idx = self.operands.index(theFactor)
            except ValueError:
                raise ValueError("Factor is absent!")        
        return (idx, num) if alsoReturnNum else idx
    
    def pull(self, startIdx=None, endIdx=None, direction='left', assumptions=frozenset()):
        '''
        Pull a subset of consecutive operands, self.operands[startIdx:endIdx],
        to one side or another. Returns the equality that equates self to 
        this new version.  Give any assumptions necessary to prove that the 
        operands are in Complexes so that the commutation theorem is applicable.
        '''
        from proveit.basiclogic.equality.axioms import equalsReflexivity
        if direction == "left": # pull the factor(s) to the left
            if startIdx == 0 or startIdx is None:
                return equalsReflexivity.specialize({x:self}).checked() # no move necessary
            return self.commute(None, startIdx, startIdx, endIdx, assumptions=assumptions)
        elif direction == "right": # pull the factor(s) to the right
            if endIdx == len(self.operands) or endIdx is None:
                return equalsReflexivity.specialize({x:self}).checked() # no move necessary
            return self.commute(startIdx, endIdx, endIdx, None, assumptions=assumptions)
        else:
            raise ValueError("Invalid pull direction!  (Acceptable values are \"left\" and \"right\".)")

    def distribute(self, index, assumptions=frozenset()):
        r'''
        Distribute through the operand at the given index.  
        Returns the equality that equates self to this new version.
        Examples: 
            :math:`a (b + c + a) d = a b d + a c d + a a d`
            :math:`a (b - c) d = a b d - a c d`
            :math:`a \left(\sum_x f(x)\right c = \sum_x a f(x) c`
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.            
        '''
        from complex.theorems import distributeThroughSum, distributeThroughSubtract, distributeThroughSummation
        operand = self.operands[index]
        if isinstance(operand, Add):
            deduceInComplexes(self.operands, assumptions)
            return distributeThroughSum.specialize({xEtc:self.operands[:index], yEtc:self.operands[index].operands, zEtc:self.operands[index+1:]})
        elif isinstance(operand, Subtract):
            deduceInComplexes(self.operands, assumptions)
            return distributeThroughSubtract.specialize({wEtc:self.operands[:index], x:self.operands[index].operands[0], y:self.operands[index].operands[1], zEtc:self.operands[index+1:]})
        elif isinstance(operand, Summation):
            deduceInComplexes(self.operands, assumptions)
            yEtcSub = operand.indices
            Pop, Pop_sub = Operation(P, operand.indices), operand.summand
            S_sub = operand.domain
            xDummy, zDummy = self.safeDummyVars(2)
            spec1 = distributeThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, x:xDummy, z:zDummy}).checked()
            return spec1.deriveConclusion().specialize({Etcetera(xDummy):self.operands[:index], Etcetera(zDummy):self.operands[index+1:]})
        else:
            raise Exception("Unsupported operand type to distribute over: " + operand.__class__)
        
    def factor(self,theFactor,pull="left", groupFactor=True, groupRemainder=False, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this product, pulling it either to the "left" or "right".
        If "theFactor" is a product, this may factor out a subset of the operands as
        long as they are next to each other (use commute to make this happen).  If
        there are multiple occurrences, the first occurrence is used.  If groupFactor is
        True and theFactor is a product, these operands are grouped together as a sub-product.
        If groupRemainder is True and there are multiple remaining operands (those not in
        "theFactor"), then these remaining operands are grouped together as a sub-product.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        idx, num = self.index(theFactor, alsoReturnNum = True)
        eq = Equation(self.pull(idx, idx+num, pull, assumptions))
        if groupFactor and num > 1:
            if pull == 'left':  # use 0:num type of convention like standard pythong
                eq.update(eq.eqExpr.rhs.group(endIdx=num, assumptions=assumptions))
            elif pull == 'right':
                eq.update(eq.eqExpr.rhs.group(startIdx=-num, assumptions=assumptions))
        if groupRemainder and len(self.operands)-num > 1:
            # if the factor has been group, effectively there is just 1 factor operand now
            numFactorOperands = 1 if groupFactor else num
            if pull == 'left':           
                eq.update(eq.eqExpr.rhs.group(startIdx=numFactorOperands, assumptions=assumptions))
            elif pull == 'right':
                eq.update(eq.eqExpr.rhs.group(endIdx=-numFactorOperands, assumptions=assumptions))
        return eq.eqExpr.checked(assumptions)
        
    def combineExponents(self, assumptions=frozenset()):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$, 
        or equates $a^c b^c$ to $(a b)^c$.
        '''
        from complex.theorems import powOfProdRev, sumInPowRev, diffInPowRev, diffFracInPowRev
        if len(self.operands) != 2 or not isinstance(self.operands[0], Exponentiate) or not isinstance(self.operands[1], Exponentiate):
            raise Exception('Combine exponents only implemented for a product of two exponentiated operands')
        if self.operands[0].base == self.operands[1].base:
            # Same base: a^b a^c = a^{b+c}$, or something similar
            aSub = self.operands[0].base
            bSub = self.operands[0].exponent
            if isinstance(self.operands[1].exponent, Neg):
                # equate $a^b a^{-c} = a^{b-c}$
                thm = diffInPowRev
                cSub = self.operands[1].exponent.operand
            elif isinstance(self.operands[1].exponent, Fraction) and isinstance(self.operands[1].exponent.numerator, Neg):
                # equate $a^b a^{-c/d} = a^{b-c/d}$
                thm = diffFracInPowRev
                cSub = self.operands[1].exponent.numerator.operand
                dSub = self.operands[1].exponent.denominator
                deduceInComplexes([aSub, bSub, cSub, dSub], assumptions=assumptions)
                return thm.specialize({a:aSub, b:bSub, c:cSub, d:dSub})
            else:
                # standard $a^b a^c = a^{b+c}$
                thm = sumInPowRev
                cSub = self.operands[1].exponent
        elif self.operands[0].exponent == self.operands[1].exponent:
            # Same exponent: equate $a^c b^c = (a b)^c$
            thm = powOfProdRev
            aSub = self.operands[0].base
            bSub = self.operands[1].base
            cSub = self.operands[0].exponent
        else:
            raise Exception('Product is not in the correct form to combine exponents: ' + str(self))
        deduceInComplexes([aSub, bSub, cSub], assumptions=assumptions)
        return thm.specialize({a:aSub, b:bSub, c:cSub})
    
MULTIPLY = Literal(pkg, 'MULTIPLY', {STRING: r'*', LATEX: r'\cdot'}, operationMaker = lambda operands : Multiply(*operands))

class Divide(BinaryOperation, NumberOp):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        BinaryOperation.__init__(self, DIVIDE, operandA, operandB)

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import real.theorems
        if numberSet == Reals:
            return real.theorems.divideClosure
        elif numberSet == RealsPos:
            return real.theorems.dividePosClosure            
        elif numberSet == Complexes:
            return complex.theorems.divideClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.divideNotEqZero

DIVIDE = Literal(pkg, 'DIVIDE', {STRING: r'/', LATEX: r'\div'}, operationMaker = lambda operands : Divide(*operands))

class Fraction(BinaryOperation, NumberOp):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands in fraction form.
        '''
        BinaryOperation.__init__(self, FRACTION, operandA, operandB)
        self.numerator = operandA
        self.denominator = operandB

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import real.theorems
        if numberSet == Reals:
            return real.theorems.fractionClosure
        elif numberSet == RealsPos:
            return real.theorems.fractionPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.fractionClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.fractionNotEqZero
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\frac{'+self.numerator.formatted(formatType, fence=False)+'}{'+ self.denominator.formatted(formatType, fence=False)+'}'
        elif formatType == STRING:
            return Divide(self.numerator, self.denominator).formatted(STRING)
        else:
            print "BAD FORMAT TYPE"
            return None
    def cancel(self,operand, pull="left", assumptions=frozenset()):
        if not isinstance(self.numerator,Multiply):
            from proveit.number.complex.theorems import fracCancel3
            newEq0 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(self.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            deduceInComplexes(operand, assumptions)
            deduceInComplexes(newEq0.rhs.denominator.operands[1], assumptions)
            newEq1 = fracCancel3.specialize({x:operand,y:newEq0.rhs.denominator.operands[1]})
            return newEq0.applyTransitivity(newEq1)
            
        assert isinstance(self.numerator,Multiply)
        if isinstance(self.denominator,Multiply):
            from proveit.number.complex.theorems import fracCancel1
            newEq0 = self.numerator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(safeDummyVar(self),self.denominator),safeDummyVar(self)).checked(assumptions)
            newEq1 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(newEq0.rhs.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            deduceInComplexes(operand, assumptions)
            deduceInComplexes(newEq1.rhs.numerator.operands[1], assumptions)
            deduceInComplexes(newEq1.rhs.denominator.operands[1], assumptions)
            newEq2 = fracCancel1.specialize({x:operand,y:newEq1.rhs.numerator.operands[1],z:newEq1.rhs.denominator.operands[1]})
            return newEq0.applyTransitivity(newEq1).applyTransitivity(newEq2)
#            newFracIntermediate = self.numerator.factor(operand).proven().rhsSubstitute(self)
#            newFrac = self.denominator.factor(operand).proven().rhsSubstitute(newFracIntermediate)
#            numRemainingOps = newFrac.numerator.operands[1:]
#            denomRemainingOps = newFrac.denominator.operands[1:]
#            return fracCancel1.specialize({x:operand,Etcetera(y):numRemainingOps,Etcetera(z):denomRemainingOps})
        else:
            from proveit.number.complex.theorems import fracCancel2
            newEq0 = self.numerator.factor(operand,pull=pull,groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(safeDummyVar(self),self.denominator),safeDummyVar(self)).checked(assumptions)
            deduceInComplexes(operand, assumptions)   
            deduceInComplexes(newEq0.rhs.numerator.operands[1], assumptions)
            newEq1 = fracCancel2.specialize({x:operand,y:newEq0.rhs.numerator.operands[1]})
            return newEq0.applyTransitivity(newEq1)
#            newFrac = self.numerator.factor(operand).proven().rhsSubstitute(self)
#            numRemainingOps = newFrac.numerator.operands[1:]
#            return fracCancel2.specialize({x:operand,Etcetera(y):numRemainingOps})

    def distribute(self, assumptions=frozenset()):
        r'''
        Distribute the denominator through the numerate.  
        Returns the equality that equates self to this new version.
        Examples: 
            :math:`(a + b + c) / d = a / d + b / d + c / d`
            :math:`(a - b) / d = a / d - b / d`
            :math:`\left(\sum_x f(x)\right / y = \sum_x [f(x) / y]`
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.            
        '''
        from complex.theorems import distributeFractionThroughSum, distributeFractionThroughSubtract, distributeFractionThroughSummation
        if isinstance(self.numerator, Add):
            deduceInComplexes(self.operands, assumptions)
            return distributeFractionThroughSum.specialize({xEtc:self.numerator.operands, y:self.denominator})
        elif isinstance(self.numerator, Subtract):
            deduceInComplexes(self.operands, assumptions)
            return distributeFractionThroughSubtract.specialize({x:self.numerator.operands[0], y:self.numerator.operands[1], z:self.denominator})
        elif isinstance(self.numerator, Summation):
            # Should deduce in Complexes, but distributeThroughSummation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduceInComplexes(self.operands, assumptions)
            xEtcSub = self.numerator.indices
            Pop, Pop_sub = Operation(P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            return distributeFractionThroughSummation.specialize({Pop:Pop_sub, S:S_sub, xEtc:xEtcSub, z:self.denominator})
        else:
            raise Exception("Unsupported operand type to distribute over: " + self.numerator.__class__)

    def factor(self,theFactor,pull="left", groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a fraction, pulling it either to the "left" or "right".
        The factor may be a product or fraction itself.  
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''        
        from complex.theorems import fracInProdRev, prodOfFracsRev, prodOfFracsLeftNumerOneRev, prodOfFracsRightNumerOneRev
        from number import num
        dummyVar = safeDummyVar(self)
        eqns = []
        if isinstance(theFactor, Fraction):
            # factor the operand denominator out of self's denominator
            denomFactorEqn = self.denominator.factor(theFactor.denominator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
            factoredDenom = denomFactorEqn.rhs
            eqns.append(denomFactorEqn.substitution(Fraction(self.numerator, dummyVar), dummyVar))
            if theFactor.numerator != num(1) and self.numerator != num(1):
                # factor the operand numerator out of self's numerator
                numerFactorEqn = self.numerator.factor(theFactor.numerator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
                factoredNumer = numerFactorEqn.rhs
                eqns.append(numerFactorEqn.substitution(Fraction(dummyVar, factoredDenom), dummyVar))
                # factor the two fractions
                deduceInComplexes(factoredNumer.operands, assumptions)
                deduceInComplexes(factoredDenom.operands, assumptions)
                eqns.append(prodOfFracsRev.specialize({x:factoredNumer.operands[0], y:factoredNumer.operands[1], 
                                                    z:factoredDenom.operands[0], w:factoredDenom.operands[1]}))
            else:
                # special case: one of the numerators is equal to one, no numerator factoring to be done
                if (pull == 'left') == (theFactor.numerator == num(1)):
                    thm = prodOfFracsLeftNumerOneRev
                else:
                    thm = prodOfFracsRightNumerOneRev
                # factor the two fractions
                deduceInComplexes(self.numerator, assumptions)                    
                deduceInComplexes(factoredDenom.operands, assumptions)
                eqns.append(thm.specialize({x:self.numerator, y:factoredDenom.operands[0], z:factoredDenom.operands[1]}))
        else:
            numerFactorEqn = self.numerator.factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
            factoredNumer = numerFactorEqn.rhs
            eqns.append(numerFactorEqn.substitution(Fraction(dummyVar, self.denominator), dummyVar))
            # factor the numerator factor from the fraction
            deduceInComplexes(factoredNumer.operands, assumptions)                    
            deduceInComplexes(self.denominator, assumptions)
            if pull == 'left':
                wEtcSub = factoredNumer.operands[:-1]
                xSub = factoredNumer.operands[-1]
                zEtcSub = []
            elif pull == 'right':
                wEtcSub = []
                xSub = factoredNumer.operands[0]
                zEtcSub = factoredNumer.operands[1:]
            eqns.append(fracInProdRev.specialize({wEtc:wEtcSub, x:xSub, y:self.denominator, zEtc:zEtcSub}))
            num = len(theFactor.operands) if isinstance(theFactor, Multiply) else 1
            if groupFactor and num > 1:
                if pull=='left':
                    eqns.append(eqns[-1].rhs.group(endIdx=num, assumptions=assumptions))
                elif pull=='right':
                    eqns.append(eqns[-1].rhs.group(startIdx=-num, assumptions=assumptions))           
        return Equation(*eqns).eqExpr # equating the lhs of the first equation to the rhs of the last equation

FRACTION = Literal(pkg, 'FRACTION', operationMaker = lambda operands : Fraction(*operands))

class Exponentiate(BinaryOperation, NumberOp):
    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        BinaryOperation.__init__(self,EXPONENTIATE, base, exponent)
        self.base = base
        self.exponent = exponent

    def _closureTheorem(self, numberSet):
        import natural.theorems
        import real.theorems
        import complex.theorems
        if numberSet == Naturals:
            return natural.theorems.powClosure
        elif numberSet == RealsPos:
            return real.theorems.powPosClosure            
        elif numberSet == Reals:
            return real.theorems.powClosure
        elif numberSet == Complexes:
            return complex.theorems.powClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.powNotEqZero
        
    def formatted(self, formatType, fence=False):
        formattedBase = self.base.formatted(formatType, fence=True)
        if isinstance(self.base, Exponentiate) or isinstance(self.base, Fraction):
            # must fence nested powers
            if formatType == LATEX:
                formattedBase = r'\left(' + formattedBase + r'\right)'
            elif formatType == STRING:
                formattedBase = r'(' + formattedBase + r')'
        if formatType == LATEX:
            return formattedBase+'^{'+self.exponent.formatted(formatType, fence=False)+'}'
        elif formatType == STRING:
            return formattedBase+'^('+self.exponent.formatted(formatType, fence=False)+')'
        else:
            print "BAD FORMAT TYPE"
            return None
    
    def raiseExpFactor(self, expFactor, assumptions=frozenset()):
        from proveit.number.complex.theorems import powOfPow, powOfNegPow
        if isinstance(self.exponent, Neg):
            b_times_c = self.exponent.operand
            thm = powOfNegPow
        else:
            b_times_c = self.exponent
            thm = powOfPow
        if not hasattr(b_times_c, 'factor'):
            raise Exception('Exponent not factorable, may not raise the exponent factor.')
        factorEq = b_times_c.factor(expFactor, pull='right', groupRemainder=True, assumptions=assumptions)
        if factorEq.lhs != factorEq.rhs:
            # factor the exponent first, then raise this exponent factor
            factoredExpEq = factorEq.substitution(self)
            return factoredExpEq.applyTransitivity(factoredExpEq.rhs.raiseExpFactor(expFactor, assumptions=assumptions))
        deduceInComplexes([self.base, b_times_c.operands[0], b_times_c.operands[1]], assumptions)
        return thm.specialize({a:self.base, b:b_times_c.operands[0], c:b_times_c.operands[1]}).deriveReversed()

    def lowerOuterPow(self, assumptions=frozenset()):
        from proveit.number.complex.theorems import powOfPow, powOfNegPow, negPowOfPow, negPowOfNegPow
        if not isinstance(self.base, Exponentiate):
            raise Exception('May only apply lowerOuterPow to nested Exponentiate operations')
        if isinstance(self.base.exponent, Neg) and isinstance(self.exponent, Neg):
            b_, c_ = self.base.exponent.operand, self.exponent.operand
            thm = negPowOfNegPow
        elif isinstance(self.base.exponent, Neg):
            b_, c_ = self.base.exponent.operand, self.exponent
            thm = powOfNegPow
        elif isinstance(self.exponent, Neg):
            b_, c_ = self.base.exponent, self.exponent.operand
            thm = negPowOfPow
        else:
            b_, c_ = self.base.exponent, self.exponent
            thm = powOfPow
        deduceInComplexes([self.base.base, b_, c_], assumptions)
        return thm.specialize({a:self.base.base, b:b_, c:c_})
    
EXPONENTIATE = Literal(pkg, 'EXPONENTIATE', operationMaker = lambda operands : Exponentiate(*operands))

#def extractExpBase(exponentiateInstance):
#    if not isinstance(exponentiateInstance,Exponentiate):
#        raise ValueError("ExponentiateInstances is not an instance of exponentiate!")
#    else:
#        return exponentiateInstance.base

class Summation(OperationOverInstances, NumberOp):
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
        from number import infinity, zero
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
        
    def _closureTheorem(self, numberSet):
        import natural.theorems
        import real.theorems
        import complex.theorems
        '''
        if numberSet == Naturals:
            return natural.theorems.powClosure
        elif numberSet == RealsPos:
            return complex.theorems.powPosClosure            
        elif numberSet == Reals:
            return real.theorems.powClosure
        el'''
        if numberSet == Complexes:
            return complex.theorems.summationClosure
                
#        self.domain = domain#self.domain already set

    def formatted(self, formatType, fence=False):

        if isinstance(self.domain,DiscreteContiguousSet):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            formattedInner = self.operator.formatted(formatType)+r'_{'+self.index.formatted(formatType)+'='+lower+r'}'+r'^{'+upper+r'} '
            implicitIvars = self.implicitInstanceVars(formatType)
            hasExplicitIvars = (len(implicitIvars) < len(self.instanceVars))
            implicitConditions = self.implicitConditions(formatType)
            hasExplicitConditions = self.hasCondition() and (len(implicitConditions) < len(self.conditions))
            if hasExplicitConditions:
                if hasExplicitIvars: 
                    formattedInner += " | "
                formattedInner += ', '.join(condition.formatted(formatType) for condition in self.conditions if condition not in implicitConditions) 
            formattedInner += self.summand.formatted(formatType, fence=fence) 
            if fence:
                if formatType == LATEX:
                    return r'\left(' + formattedInner + r'\right)'
                else:
                    return r'(' + formattedInner + r')'
            else: return formattedInner
        else:
            return OperationOverInstances.formatted(self, formatType, fence)
        
    def reduceGeomSum(self):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        '''
        from proveit.number.theorems import infGeomSum, finGeomSum
        from number import zero, infinity
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

    def factor(self, theFactor, pull="left", groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a common factor from a summation, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from complex.theorems import distributeThroughSummationRev
        if not theFactor.freeVars().isdisjoint(self.indices):
            raise Exception('Cannot factor anything involving summation indices out of a summation')
        # We need to deduce that the summands are all in Complexes.  We prove that as a side-effect when
        # we deduce that the summation is in Complexes.
        self.deduceInComplexes(assumptions=assumptions)
        # We may need to factor the summand within the summation
        summand_assumptions = assumptions | set([In(index, self.domain) for index in self.indices])
        summandFactorEq = self.summand.factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=summand_assumptions)
        summandInstanceEquivalence = summandFactorEq.generalize(self.indices, domain=self.domain).checked(assumptions)
        eq = Equation(self.instanceSubstitution(summandInstanceEquivalence).checked(assumptions))
        factorOperands = theFactor.operands if isinstance(theFactor, Multiply) else theFactor
        xDummy, zDummy = self.safeDummyVars(2)
        # Now do the actual factoring by reversing distribution
        if pull == 'left':
            Pop, Pop_sub = Operation(P, self.indices), summandFactorEq.rhs.operands[-1]
            xSub = factorOperands
            zSub = []
        elif pull == 'right':
            Pop, Pop_sub = Operation(P, self.indices), summandFactorEq.rhs.operands[0]
            xSub = []
            zSub = factorOperands
        spec1 = distributeThroughSummationRev.specialize({Pop:Pop_sub, S:self.domain, yEtc:self.indices, x:xDummy, z:zDummy}).checked()
        eq.update(spec1.deriveConclusion().specialize({Etcetera(xDummy):xSub, Etcetera(zDummy):zSub}))
        deduceInComplexes(eq.eqExpr.rhs, assumptions)
        if groupFactor and len(factorOperands) > 1:
            eq.update(eq.eqExpr.rhs.group(endIdx=len(factorOperands), assumptions=assumptions))
        return eq.eqExpr #.checked(assumptions)
            
def summationMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return Summation(params['instanceVars'],params['instanceExpr'],params['domain'],params['conditions'])

    
#SUMMATION = Literal(pkg, "SUMMATION", {STRING: r'Summation', LATEX: r'\sum'}, operationMaker = lambda operands : Summation(*OperationOverInstances.extractParameters(operands)))

SUMMATION = Literal(pkg, "SUMMATION", {STRING: r'Summation', LATEX: r'\sum'}, operationMaker = summationMaker)

class Neg(Operation, NumberOp):
    def __init__(self,A):
        Operation.__init__(self, NEG, A)
        self.operand = A
        #NumberOp.__init__(self, {Complexes:complex.theorems.negClosure})

    def _closureTheorem(self, numberSet):
        import complex.theorems
        import integer.theorems
        if numberSet == Complexes:
            return complex.theorems.negClosure
        elif numberSet == Integers:
            return integer.theorems.negClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.negNotEqZero
    
    def formatted(self, formatType, fence=False):
        outStr = ''
        if fence: outStr += r'\left(' if formatType == LATEX else r'('
        outStr += ('-'+self.operand.formatted(formatType, fence=True))
        if fence: outStr += r'\right)' if formatType == LATEX else r')'
        return outStr

    def factor(self,operand,pull="left", groupFactor=None, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a negated expression, pulling it either to the "left" or "right".
        groupFactor and groupRemainder are not relevant but kept for compatibility with 
        other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from complex.theorems import negTimesPosRev, posTimesNegRev
        if isinstance(operand, Neg):
            if pull == 'left':
                thm = negTimesPosRev
            else:
                thm = posTimesNegRev
            operand = operand.operand
        else:
            if pull == 'left':
                thm = posTimesNegRev
            else:
                thm = negTimesPosRev
        operandFactorEqn = self.operand.factor(operand, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
        # in this instance, the automated way is safe because there is no other operand:
        eqn1 = operandFactorEqn.substitution(self) 
        deduceInComplexes(operandFactorEqn.rhs.operands, assumptions)
        eqn2 = thm.specialize({x:operandFactorEqn.rhs.operands[0], y:operandFactorEqn.rhs.operands[1]})
        return eqn1.applyTransitivity(eqn2)
        
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
        from number import infinity
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
