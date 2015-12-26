import sys
from proveit.expression import Literal, LATEX, STRING, Operation, Variable, safeDummyVar
from proveit.multiExpression import MultiVariable, Etcetera
from proveit.basiclogic import Equals, Equation, Forall, In
#from proveit.number import axioms
#from proveit.statement import *
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation, OperationOverInstances
from proveit.everythingLiteral import EVERYTHING
from proveit.common import a, b, c, d, f, k, l, m, n, r, v, w, x, y, z, A, P, S, aEtc, cEtc, vEtc, wEtc, xEtc, yEtc, zEtc
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

    def deduceElemInSet(self, member):
        from integer.theorems import inInterval
        return inInterval.specialize({a:self.lowerBound, b:self.upperBound, n:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from integer.theorems import intervalLowerBound
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return intervalLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from integer.theorems import intervalUpperBound
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return intervalUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from integer.theorems import allInDiscreteInterval_InInts
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InInts.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturals(self, member, assumptions=frozenset()):
        from natural.theorems import allInDiscreteInterval_InNats
        from numberSets import deduceInNaturals
        deduceInNaturals(self.lowerBound, assumptions=assumptions)
        deduceInNaturals(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InNats.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturalsPos(self, member, assumptions=frozenset()):
        from natural.theorems import allInDiscreteInterval_InNatsPos
        from numberSets import deduceInNaturalsPos
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deducePositive(self.lowerBound, assumptions=assumptions)
        return allInDiscreteInterval_InNatsPos.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberIsPositive(self, member, assumptions=frozenset()):
        from integer.theorems import allInPositiveIntervalArePositive
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deducePositive(self.lowerBound, assumptions=assumptions)
        return allInPositiveIntervalArePositive.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        
        
    def deduceMemberIsNegative(self, member, assumptions=frozenset()):
        from integer.theorems import allInNegativeIntervalAreNegative
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deduceNegative(self.upperBound, assumptions=assumptions)
        return allInNegativeIntervalAreNegative.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        

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

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalOO
        return inIntervalOO.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOOLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOOLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOOUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOOUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalOO_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalOO_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalOO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalOO.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceLeftRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOOleft
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOOleft.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRightRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOOright
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOOright.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
        

INTERVALOO = Literal(pkg, 'INTERVALOO', operationMaker = lambda operands : IntervalOO(*operands))


class IntervalOC(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALOC,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right]'
        else:
            return r'('+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r']'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalOC
        return inIntervalOC.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOCLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOCLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOCUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOCUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalOC_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalOC_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalOC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalOC.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOC.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})


INTERVALOC = Literal(pkg, 'INTERVALOC', operationMaker = lambda operands : IntervalOC(*operands))

class IntervalCO(Interval):

    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALCO,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right)'
        else:
            return r'['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r')'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalCO
        return inIntervalCO.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCOLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCOLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCOUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCOUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalCO_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalCO_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalCO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalCO.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalCO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalCO.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})


INTERVALCO = Literal(pkg, 'INTERVALCO', operationMaker = lambda operands : IntervalCO(*operands))

class IntervalCC(Interval):
    
    def __init__(self,lowerBound,upperBound):
        Interval.__init__(self,INTERVALCC,lowerBound,upperBound)
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\left['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r'\right]'
        else:
            return r'['+self.lowerBound.formatted(formatType,fence=fence)+r','+self.upperBound.formatted(formatType,fence=fence)+r']'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalCC
        return inIntervalCC.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCCLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCCLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCCUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCCUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalCC_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalCC_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalCC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalCC.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

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

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        raise NotImplementedError('deriveShifted is implemented for each specific OrderingRelation')

    def deriveAdded(self, otherOrderingRelation, assumptions=frozenset()):
        r'''
        Add this ordering relation with another ordering relation.
        For example, if self is (a < b) and otherOrderingRelation is (c < d), then
        this derives and returns (a + c < b + d).
        '''
        other = otherOrderingRelation
        if not (isinstance(other, OrderingRelation)):
            raise ValueError("Expecting 'otherOrderingRelation' to be an OrderingRelation")
        if (isinstance(self, LessThan) or isinstance(self, LessThanEquals)) != (isinstance(other, LessThan) or isinstance(other, LessThanEquals)):
            # reverse other to be consistent with self (both less than type or greater than type)
            other = other.deriveReversed()
        shiftedSelf = self.deriveShifted(other.lhs, 'right', assumptions) # e.g., a + c < b + c
        shiftedOther = other.deriveShifted(self.rhs, 'left', assumptions) # e.g., b + c < b + d
        return shiftedSelf.applyTransitivity(shiftedOther) # e.g., a + c < b + d

class LessThan(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at bigger than first.
        '''
        OrderingRelation.__init__(self, LESSTHAN,lhs,rhs)
        
    def deduceInBooleans(self, assumptions=frozenset()):
        from real.theorems import lessThanInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)

    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a < b to a <= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from real.theorems import relaxLessThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return relaxLessThan.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
        
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
                #print self,result
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

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a < b`, derive and return :math:`-a > -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from real.theorems import negatedLessThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedLessThan.specialize({a:self.lhs, b:self.rhs})
        
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a < b`, derive and return :math:`a + c < b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from real.theorems import lessThanAddRight, lessThanAddLeft, lessThanSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return lessThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return lessThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

LESSTHAN = Literal(pkg,'LESSTHAN', {STRING: r'<', LATEX:r'<'}, operationMaker = lambda operands : LessThan(*operands))

class LessThanEquals(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at least as big as first.
        '''
        OrderingRelation.__init__(self, LESSTHANEQUALS,lhs,rhs)
        
    def deduceInBooleans(self, assumptions=frozenset()):
        from real.theorems import lessThanEqualsInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
    
    def unfold(self, assumptions=frozenset()):
        from real.axioms import lessThanEqualsDef
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanEqualsDef.specialize({x:self.lhs, y:self.rhs})
    
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

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \leq b`, derive and return :math:`-a \geq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from real.theorems import negatedLessThanEquals
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedLessThanEquals.specialize({a:self.lhs, b:self.rhs})
    
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \leq b`, derive and return :math:`a + c \leq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from real.theorems import lessThanEqualsAddRight, lessThanEqualsAddLeft, lessThanEqualsSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return lessThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return lessThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))
        
LESSTHANEQUALS = Literal(pkg,'LESSTHANEQUALS', {STRING: r'<=', LATEX:r'\leq'}, operationMaker = lambda operands : LessThanEquals(*operands))


class GreaterThan(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, GREATERTHAN,lhs,rhs)
        
    def deduceInBooleans(self, assumptions=frozenset()):
        from real.theorems import greaterThanInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
    
    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a > b to a >= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from real.theorems import relaxGreaterThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return relaxGreaterThan.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
        
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

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a > b`, derive and return :math:`-a < -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from real.theorems import negatedGreaterThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedGreaterThan.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a > b`, derive and return :math:`a + c > b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from real.theorems import greaterThanAddRight, greaterThanAddLeft, greaterThanSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return greaterThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return greaterThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

GREATERTHAN = Literal(pkg,'GREATERTHAN', {STRING: r'>', LATEX:r'>'}, operationMaker = lambda operands : GreaterThan(*operands))

class GreaterThanEquals(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, GREATERTHANEQUALS,lhs,rhs)

    def deduceInBooleans(self, assumptions=frozenset()):
        from real.theorems import greaterThanEqualsInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)

    def unfold(self, assumptions=frozenset()):
        from real.axioms import greaterThanEqualsDef
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanEqualsDef.specialize({x:self.lhs, y:self.rhs})
    
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

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \geq b`, derive and return :math:`-a \leq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from real.theorems import negatedGreaterThanEquals
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedGreaterThanEquals.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \geq b`, derive and return :math:`a + c \geq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from real.theorems import greaterThanEqualsAddRight, greaterThanEqualsAddLeft, greaterThanEqualsSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return greaterThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return greaterThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

GREATERTHANEQUALS = Literal(pkg,'GREATERTHANEQUALS', {STRING: r'>=', LATEX:r'\geq'}, operationMaker = lambda operands : GreaterThanEquals(*operands))

class Min(Operation, NumberOp):
    def __init__(self, A, B):
        Operation.__init__(self, MIN, [A, B])

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Reals:
            return real.theorems.minClosure
        elif numberSet == RealsPos:
            return real.theorems.minPosClosure            

MIN = Literal(pkg, 'MIN', {STRING:'Min', LATEX:r'{\rm Min}'}, operationMaker = lambda operands : Min(*operands))

class Max(Operation, NumberOp):
    def __init__(self, A, B):
        Operation.__init__(self, MAX, [A, B])

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Reals:
            return real.theorems.maxClosure
        elif numberSet == RealsPos:
            return real.theorems.maxPosClosure               

MAX = Literal(pkg, 'MAX', {STRING:'Max', LATEX:r'{\rm Max}'}, operationMaker = lambda operands : Max(*operands))

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

    def deduceGreaterThanEqualsZero(self, assumptions=frozenset()):
        from complex.theorems import absIsNonNeg
        deduceInComplexes(self.operand, assumptions)
        return absIsNonNeg.specialize({a:self.operand}).checked(assumptions)
    
    def distribute(self, assumptions=frozenset()):
        '''
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are in complexes.
        '''
        from complex.theorems import absFrac, absProd
        if isinstance(self.operand, Fraction):
            deduceInComplexes(self.operand.numerator, assumptions)
            deduceInComplexes(self.operand.denominator, assumptions)
            return absFrac.specialize({a:self.operand.numerator, b:self.operand.denominator}).checked(assumptions)
        elif isinstance(self.operand, Multiply):
            deduceInComplexes(self.operand.operands, assumptions)
            return absProd.specialize({xEtc:self.operand.operands}).checked(assumptions)
        else:
            raise ValueError('Unsupported operand type for absolution value distribution: ', str(self.operand.__class__))
    
    def absElimination(self, assumptions=frozenset()):
        '''
        For some |x| expression, deduce |x| = x after trying to deduce x >= 0.
        Assumptions may be needed to deduce x >= 0.
        '''
        from real.theorems import absElim
        # deduceNonNeg(self.operand, assumptions) # NOT YET IMPLEMENTED
        return absElim.specialize({x:self.operand})
        

ABS = Literal(pkg, 'ABS', operationMaker = lambda operands : Abs(*operands))

class Add(AssociativeOperation, NumberOp):
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        AssociativeOperation.__init__(self, ADD, *operands)
        self.terms = self.operands

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

    def simplification(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive and return this Add expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from complex.theorems import addZero
        from number import zero
        eq = Equation()
        expr = self
        try:
            zeroIdx = expr.operands.index(zero)
            # there is a zero in the sum.  We can simplify that.
            if zeroIdx > 0:
                # commute it so that the zero comes first
                expr = eq.update(expr.commute(0, zeroIdx, zeroIdx, zeroIdx+1, assumptions)).rhs
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(addZero.specialize({x:expr.operands[1]}))
        except ValueError:
            raise ValueError('Only trivial simplification is implemented (zero term)')
        
    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive this Add expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    
    def subtractionFolding(self, termIdx=None, assumptions=frozenset()):
        '''
        Given a negated term, termIdx or the first negated term if termIdx is None,
        deduce the equivalence between self and a Subtract form (with the specified
        negated term on the right of the subtraction).  Assumptions
        may be necessary to deduce operands being in the set of Complexes.
        '''
        from complex.theorems import addNegAsSubtract
        if termIdx is None:
            for k, term in enumerate(self.terms):
                if isinstance(term, Neg):
                    termIdx = k
                    break
            if termIdx is None:
                raise Exception("No negated term, can't provide the subtraction folding.")
        if not isinstance(self.terms[termIdx], Neg):
            raise ValueError("Specified term is not negated, can't provide the subtraction folding.")
        expr = self
        if termIdx != -1 and termIdx != len(expr.terms)-1:
            # put the negative term at the end
            expr = expr.commute(termIdx, termIdx+1, -1)
        if len(expr.terms) > 2:
            # group all of the other terms
            expr = expr.group(0, -1)
        deduceInComplexes(expr.operands[0], assumptions)
        deduceInComplexes(expr.operands[-1].operand, assumptions)
        return addNegAsSubtract.specialize({x:expr.operands[0], y:expr.operands[-1].operand})
    
    def deduceInNaturalsPosDirectly(self, assumptions=frozenset(), ruledOutSets=frozenset(), dontTryPos=False, dontTryNeg=False):
        '''
        If all of the terms are in Naturals and just one is positive, then the sum is positive.
        '''
        from numberSets import DeduceInNumberSetException
        from natural.theorems import sumInNatsPos
        
        # first make sure all the terms are in Naturals
        for term in self.operands:
            deduceInNaturals(term, assumptions) 
        for k, term in enumerate(self.operands):
            try:
                # found one positive term to make the sum positive
                deducePositive(term, assumptions)
                return sumInNatsPos.specialize({aEtc:self.operands[:k], b:term, cEtc:self.operands[k+1:]}).checked(assumptions)
            except:
                pass
        # need to have one of the elements positive for the sum to be positive
        raise DeduceInNumberSetException(self, NaturalsPos, assumptions)

    def deduceStrictIncrease(self, lowerBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsPos, deduce an return
        the statement that the sum is greater than the term at lowerBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from real.theorems import strictlyIncreasingAdditions        
        for i, term in enumerate(self.terms):
            if i == lowerBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsPos(term, assumptions)
        return strictlyIncreasingAdditions.specialize({aEtc:self.terms[:lowerBoundTermIndex], cEtc:self.terms[lowerBoundTermIndex+1:]}).specialize({b:self.terms[lowerBoundTermIndex]}).checked(assumptions)

    def deduceStrictDecrease(self, upperBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsNeg, deduce an return
        the statement that the sum is less than the term at upperBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from real.theorems import strictlyDecreasingAdditions        
        for i, term in enumerate(self.terms):
            if i == upperBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsNeg(term, assumptions)
        return strictlyDecreasingAdditions.specialize({aEtc:self.terms[:upperBoundTermIndex], cEtc:self.terms[upperBoundTermIndex+1:]}).specialize({b:self.terms[upperBoundTermIndex]}).checked(assumptions)
        
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from proveit.number.complex.theorems import addComm
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
        return addComm.specialize({vEtc:vSub, wEtc:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)
    
    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-sum wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from proveit.number.axioms import addAssoc
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

        from proveit.number.theorems import addAssocRev
        deduceInComplexes(self.operands, assumptions)
        deduceInComplexes(self.operands[idx].operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return addAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def factor(self, theFactor, pull="left", groupFactor=True, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this sum, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, these operands are grouped 
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from complex.theorems import distributeThroughSumRev
        expr = self
        eq = Equation()
        dummyVar = self.safeDummyVar()
        yEtcSub = []
        for i, term in enumerate(self.terms):
            sumWithDummy = Add(*[jterm if j != i else dummyVar for j, jterm in enumerate(expr.terms)])
            termFactorization = term.factor(theFactor, pull, groupFactor=groupFactor, groupRemainder=True, assumptions=assumptions)
            if not isinstance(termFactorization.rhs, Multiply):
                raise Exception('Expecting right hand size of factorization to be a product')
            if pull == 'left':
                # the grouped remainder on the right
                yEtcSub.append(termFactorization.rhs.operands[-1]) 
            else:
                # the grouped remainder on the left
                yEtcSub.append(termFactorization.rhs.operands[0])
            eq.update(termFactorization.substitution(sumWithDummy, dummyVar))
            expr = eq.eqExpr.rhs
        if not groupFactor and isinstance(theFactor, Multiply):
            factorSub = theFactor.operands
        else:
            factorSub = [theFactor]
        deduceInComplexes(factorSub, assumptions=assumptions)
        deduceInComplexes(yEtcSub, assumptions=assumptions)
        if pull == 'left':
            xEtcSub = factorSub
            zEtcSub = []
        else:
            xEtcSub = []
            zEtcSub = factorSub
        eq.update(distributeThroughSumRev.specialize({xEtc:xEtcSub, yEtc:yEtcSub, zEtc:zEtcSub}))
        return eq.eqExpr.checked(assumptions)
    
    def join(self, assumptions=frozenset()):
        '''
        For joining two summations (could be more sophistocated later).
        '''
        if len(self.terms) != 2 or not all(isinstance(term, Summation) for term in self.terms):
            raise Exception("Sum joinoing currently only implemented for two summation terms.")
        return self.terms[0].join(self.terms[1], assumptions)

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
        import natural.theorems
        import integer.theorems        
        from number import one
        if numberSet == Reals:
            return real.theorems.subtractClosure
        elif numberSet == Complexes:
            return complex.theorems.subtractClosure
        elif numberSet == Integers:
            return integer.theorems.subtractClosure
        elif numberSet == Naturals:
            return integer.theorems.subtractClosureNats
        elif numberSet == NaturalsPos:
            return integer.theorems.subtractClosureNatsPos
            
    
    def _notEqZeroTheorem(self):
        from complex.theorems import diffNotEqZero
        # Can derive (a - b) != 0 given a != b.
        # Derive a != b from b != a in case we have proven b != a instead of a != b.
        NotEquals(self.operands[1], self.operands[0]).deriveReversed()
        return diffNotEqZero
    
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
    
    def convertToAdd(self, assumptions=frozenset()):
        '''
        Given (x - y) deduce and return (x - y) = (x + (-y)).
        Assumptions may be needed to deduce that the operands are in Complexes.
        '''
        from complex.theorems import subtractAsAddNeg
        deduceInComplexes(self.operands, assumptions)
        return subtractAsAddNeg.specialize({x:self.operands[0], y:self.operands[1]}).checked(assumptions)

    def distribute(self, assumptions=frozenset()):
        '''
        Given something of the form (a + b + ...) - (x + y + ...), deduce and return
        (a + b + ...) - (x + y + ...) = a + b + ... + (-x) + (-y) + ....
        Assumptions may be needed to deduce that the operands are in Complexes.        
        '''
        # first deduce: (a + b + ...) - (x + y + ...)  = (a + b + ...) + (-x) + (-y) + ...
        eqn = Equation()
        if isinstance(self.operands[1], Add):
            from complex.theorems import distributeSubtraction
            deduceInComplexes(self.operands[0], assumptions)
            deduceInComplexes(self.operands[1].operands, assumptions)
            eqn.update(distributeSubtraction.specialize({x:self.operands[0], yEtc:self.operands[1].operands}).checked(assumptions))
        else:
            eqn.update(self.convertToAdd(assumptions))
        expr = eqn.eqExpr.rhs
        dummyVar = expr.safeDummyVar()
        # next try to simplify any of the negated terms
        negatedTerms = [term for term in expr.operands[1:]]
        for k, negatedTerm in enumerate(negatedTerms):
            try:
                negTermSimplification = negatedTerm.simplification(assumptions)
                eqn.update(negTermSimplification.substitution(Add(*(expr.terms[:k+1] + [dummyVar] + expr.terms[k+2:])), dummyVar)).checked(assumptions)
                expr = eqn.eqExpr.rhs
            except:
                pass # skip over 
        # ungroup the first part if it is a sum: (a + b + ...) + (-x) + (-y) + ... = a + b + ... + (-x) + (-y) + ...
        if isinstance(self.operands[0], Add):
            eqn.update(expr.applyTransitivity(expr.ungroup(0)).checked(assumptions))
        return eqn.eqExpr

    def cancel(self, assumptions=frozenset()):
        '''
        Attempt to cancel any term of a subtraction and return the resulting equivalence.
        The first term on the left that is the same as on the right will be canceled.
        Assumptions may be needed to deduce that the operands are in Complexes.        
        '''
        from complex.theorems import subtractCancelElimSums, subtractCancelElimLeftSum, subtractCancelElimRightSum
        from complex.theorems import subtractCancelTwoSums, subtractCancelLeftSum, subtractCancelRightSum
        from complex.theorems import subtractCancelLeftSumSingleRight, subtractCancelLeftSumSingleLeft, subtractCancelRightSumSingleRight, subtractCancelRightSumSingleLeft 
        from complex.theorems import subtractCancelComplete
        from number import zero
        dummy = self.safeDummyVar()
        eq = Equation()
        expr = self
        if self.operands[0] == self.operands[1]:
            # x - x = 0
            deduceInComplexes(self.operands[0], assumptions)
            return subtractCancelComplete.specialize({x:self.operands[0]}).checked(assumptions)
        if isinstance(expr.operands[0], Subtract):
            eq.update(expr.operands[0].convertToAdd(assumptions=assumptions).substitution(Subtract(dummy, expr.operands[1]), dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[1], Subtract):
            eq.update(expr.operands[1].convertToAdd(assumptions=assumptions).substitution(Subtract(expr.operands[0], dummy), dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[0], Add):
            if isinstance(expr.operands[1], Add):
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)                
                foundOne = False
                for idx1 in xrange(len(expr.operands[0].operands)):
                    try:
                        idx2 = expr.operands[1].operands.index(expr.operands[0].operands[idx1])
                        foundOne = True
                        break
                    except:
                        pass
                if not foundOne:
                    raise Exception("No common term found")
                wSub = expr.operands[0].operands[idx1]
                try:
                    idx2 = expr.operands[1].operands.index(wSub)
                except:
                    raise Exception(str(wSub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")
                if len(expr.operands[0].operands) == 2 and len(expr.operands[1].operands) == 2:
                    # special case where Add on both sides is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(Subtract(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(Subtract(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[0] # the form we were supposed to get to
                    eq.update(subtractCancelElimSums.specialize({x:expr.operands[0].operands[0], y:expr.operands[0].operands[1], z:expr.operands[1].operands[1]}))
                elif len(expr.operands[0].operands) == 2:
                    # special case where Add on the left is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(Subtract(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[idx2] # the form we were supposed to get to
                    wSub = expr.operands[0].operands[0]
                    xSub = expr.operands[0].operands[1]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2+1:]
                    eq.update(subtractCancelElimLeftSum.specialize({w:wSub, x:xSub, yEtc:ySub, zEtc:zSub}))
                elif len(expr.operands[1].operands) == 2:
                    # special case where Add on the right is eliminated
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(Subtract(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[1].operands[0] == expr.operands[0].operands[idx1] # the form we were supposed to get to
                    wSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1]
                    ySub = expr.operands[0].operands[idx1+1:]
                    zSub = expr.operands[1].operands[1]
                    eq.update(subtractCancelElimRightSum.specialize({wEtc:wSub, x:xSub, yEtc:ySub, z:zSub}))
                else:
                    vSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1+1:]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2+1:]
                    eq.update(subtractCancelTwoSums.specialize({vEtc:vSub, w:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions))
            else:
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1], assumptions=assumptions)                
                ySub = expr.operands[1]
                try:
                    idx1 = expr.operands[0].operands.index(ySub)
                except:
                    raise Exception(str(ySub) + " not found in " + str(expr.operands[0]) + " for a subtraction cancel")                    
                if len(expr.operands[0].operands) == 2:
                    # only one term remains
                    if idx1 == 0:
                        eq.update(subtractCancelLeftSumSingleRight.specialize({y:ySub, x:expr.operands[0].operands[1]})).checked(assumptions)
                    else:
                        eq.update(subtractCancelLeftSumSingleLeft.specialize({y:ySub, x:expr.operands[0].operands[0]})).checked(assumptions)                        
                else:
                    xSub = expr.operands[0].operands[:idx1]
                    zSub = expr.operands[0].operands[idx1+1:]
                    eq.update(subtractCancelLeftSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions))
        else:
            deduceInComplexes(expr.operands[0], assumptions=assumptions)
            deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)                
            ySub = expr.operands[0]
            try:
                idx2 = expr.operands[1].operands.index(ySub)
            except:
                raise Exception(str(ySub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")                    
            if len(expr.operands[1].operands) == 2:
                # only one term remains
                if idx2 == 0:
                    eq.update(subtractCancelRightSumSingleRight.specialize({y:ySub, x:expr.operands[1].operands[1]})).checked(assumptions)
                else:
                    eq.update(subtractCancelRightSumSingleLeft.specialize({y:ySub, x:expr.operands[1].operands[0]})).checked(assumptions)                        
            else:
                xSub = expr.operands[1].operands[:idx2]
                zSub = expr.operands[1].operands[idx2+1:]
                eq.update(subtractCancelRightSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions))
        if isinstance(eq.eqExpr.rhs, Neg) and (isinstance(eq.eqExpr.rhs.operand, Neg) or eq.eqExpr.rhs.operand == zero):
            eq.update(eq.eqExpr.rhs.simplification(assumptions)) # take care of double negation or zero negation
        return eq.eqExpr

SUBTRACT = Literal(pkg, 'SUBTRACT', {STRING: r'-', LATEX: r'-'}, operationMaker = lambda operands : Subtract(*operands))

class Multiply(AssociativeOperation, NumberOp):
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        AssociativeOperation.__init__(self, MULTIPLY, *operands)
        self.factors = operands

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
    
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one factor,
        derive and return this multiplication expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from complex.theorems import multOne, multZero
        from number import zero, one
        eq = Equation()
        expr = self
        try:
            zeroIdx = self.operands.index(zero)
            # there is a zero in the product.  We can simplify that.
            if zeroIdx > 0:
                # commute it so that the zero comes first
                expr = eq.update(expr.commute(0, zeroIdx, zeroIdx, zeroIdx+1, assumptions)).rhs
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(multZero.specialize({x:expr.operands[1]}))
        except ValueError:
            pass # no zero factor
        try:
            oneIdx = expr.operands.index(one)
            # there is a one in the product.  We can simplify that.
            if oneIdx > 0:
                # commute it so that the one comes first
                expr = eq.update(expr.commute(0, oneIdx, oneIdx, oneIdx+1, assumptions)).rhs                
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(multOne.specialize({x:expr.operands[1]}))
        except ValueError:
            pass # no one factor
        raise ValueError('Only trivial simplification is implemented (zero or one factors)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one factor,
        derive this multiplication expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
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
        from proveit.number.axioms import multAssoc
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

        from proveit.number.theorems import multAssocRev
        deduceInComplexes(self.operands, assumptions)
        deduceInComplexes(self.operands[idx].operands, assumptions)
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

    def distribute(self, index=None, assumptions=frozenset()):
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
        from complex.theorems import fracInProd, prodOfFracs
        if index is None and len(self.factors) == 2 and all(isinstance(factor, Fraction) for factor in self.factors):
            deduceInComplexes(self.factors[0].operands, assumptions)
            deduceInComplexes(self.factors[1].operands, assumptions)
            return prodOfFracs.specialize({x:self.factors[0].numerator, y:self.factors[1].numerator, z:self.factors[0].denominator, w:self.factors[1].denominator})
        operand = self.operands[index]
        if isinstance(operand, Add):
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            return distributeThroughSum.specialize({xEtc:self.operands[:index], yEtc:self.operands[index].operands, zEtc:self.operands[index+1:]})
        elif isinstance(operand, Subtract):
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            return distributeThroughSubtract.specialize({wEtc:self.operands[:index], x:self.operands[index].operands[0], y:self.operands[index].operands[1], zEtc:self.operands[index+1:]})
        elif isinstance(operand, Fraction):            
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            eqn = fracInProd.specialize({wEtc:self.operands[:index], x:self.operands[index].operands[0], y:self.operands[index].operands[1], zEtc:self.operands[index+1:]})            
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numerSimplification = eqn.rhs.numerator.simplification(assumptions=assumptions)
                dummyVar = eqn.safeDummyVar()
                return numerSimplification.rhsSubstitute(Equals(eqn.lhs, Fraction(dummyVar, eqn.rhs.denominator)), dummyVar)
            except:
                return eqn
        elif isinstance(operand, Summation):
            deduceInComplexes(self.operands, assumptions)
            yEtcSub = operand.indices
            Pop, Pop_sub = Operation(P, operand.indices), operand.summand
            S_sub = operand.domain
            xDummy, zDummy = self.safeDummyVars(2)
            spec1 = distributeThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, 
                                                           xEtc:Etcetera(MultiVariable(xDummy)), zEtc:Etcetera(MultiVariable(zDummy))}).checked()
            return spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):self.operands[:index], \
                                                        Etcetera(MultiVariable(zDummy)):self.operands[index+1:]})
        else:
            raise Exception("Unsupported operand type to distribute over: " + str(operand.__class__))
        
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
        
    def combineExponents(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$,  $a^b a$ to $a^{b+1}, $a a^b$ to $a^{1+b},
        or equates $a^c b^c$ to $(a b)^c$.
        '''
        from complex.theorems import powOfPositivesProdRev, intPowOfProdRev, natsPosPowOfProdRev
        from complex.theorems import sumInPowRev, diffInPowRev, diffFracInPowRev
        from complex.theorems import addOneRightInPowRev, addOneLeftInPowRev
        from real.theorems import prodOfSqrts
        if startIdx is not None or endIdx is not None:
            dummyVar = self.safeDummyVar()
            grouped = self.group(startIdx, endIdx, assumptions=assumptions)
            innerCombineExponents = grouped.rhs.factors[startIdx].combineExponents(assumptions=assumptions)
            combineInGroup = innerCombineExponents.substitution(Multiply(*(self.factors[:startIdx] + (dummyVar,) + self.factors[endIdx:])), dummyVar)
            return grouped.applyTransitivity(combineInGroup)
        if all(isinstance(factor, Sqrt) for factor in self.factors):
            # combine the square roots into one square root
            factorBases = [factor.base for factor in self.factors]
            deduceInRealsPos(factorBases, assumptions)
            return prodOfSqrts.specialize({xEtc:factorBases})
        if len(self.operands) != 2 or not isinstance(self.operands[0], Exponentiate) or not isinstance(self.operands[1], Exponentiate):
            if len(self.operands) == 2 and isinstance(self.operands[0], Exponentiate) and self.operands[0].base == self.operands[1]:
                # Of the form a^b a
                deduceInComplexes(self.operands[1], assumptions)
                deduceNotZero(self.operands[1], assumptions)
                deduceInComplexes(self.operands[0].exponent, assumptions)
                return addOneRightInPowRev.specialize({a:self.operands[1], b:self.operands[0].exponent})
            elif len(self.operands) == 2 and isinstance(self.operands[1], Exponentiate) and self.operands[1].base == self.operands[0]:
                # Of the form a a^b
                deduceInComplexes(self.operands[0], assumptions)
                deduceNotZero(self.operands[0], assumptions)
                deduceInComplexes(self.operands[1].exponent, assumptions)
                return addOneLeftInPowRev.specialize({a:self.operands[0], b:self.operands[1].exponent})
            raise Exception('Combine exponents only implemented for a product of two exponentiated operands (or a simple variant)')
        if self.operands[0].base == self.operands[1].base:
            # Same base: a^b a^c = a^{b+c}$, or something similar
            aSub = self.operands[0].base
            deduceNotZero(aSub, assumptions)
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
            aSub = self.operands[0].base
            bSub = self.operands[1].base
            expSub = self.operands[0].exponent
            try:
                deduceInNaturalsPos(expSub, assumptions)
                deduceInComplexes([aSub, bSub], assumptions)
                return natsPosPowOfProdRev.specialize({n:expSub}).specialize({a:aSub, b:bSub})
            except:
                pass
            try:
                deduceInIntegers(expSub, assumptions)
                deduceInComplexes([aSub, bSub], assumptions)
                deduceNotZero([aSub, bSub], assumptions)
                return intPowOfProdRev.specialize({n:expSub}).specialize({a:aSub, b:bSub})
            except:
                deduceInRealsPos([aSub, bSub], assumptions)
                deduceInComplexes([expSub], assumptions)
                return powOfPositivesProdRev.specialize({c:expSub}).specialize({a:aSub, b:bSub})
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

    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero numerator or one denominator,
        derive and return this fraction expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from complex.theorems import fracZeroNumer, fracOneDenom
        from number import zero, one
        if self.numerator == zero:
            deduceInComplexes(self.denominator, assumptions)
            return fracZeroNumer.specialize({x:self.denominator})
        elif self.denominator == one:
            deduceInComplexes(self.numerator, assumptions)
            return fracOneDenom.specialize({x:self.numerator})
        raise ValueError('Only trivial simplification is implemented (zero or one factors)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero numerator or one denominator,
        derive this fraction expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\frac{'+self.numerator.formatted(formatType, fence=False)+'}{'+ self.denominator.formatted(formatType, fence=False)+'}'
        elif formatType == STRING:
            return Divide(self.numerator, self.denominator).formatted(STRING)
        else:
            print "BAD FORMAT TYPE"
            return None
    
    def combineExponents(self, assumptions=frozenset()):
        from complex.theorems import fracIntExp, fracNatPosExp
        if isinstance(self.numerator, Exponentiate) and isinstance(self.denominator, Exponentiate):
            if self.numerator.exponent == self.denominator.exponent:
                exponent = self.numerator.exponent
                try:
                    deduceInNaturalsPos(exponent, assumptions)
                    deduceInComplexes([self.numerator.base, self.denominator.base], assumptions)
                    deduceNotZero(self.denominator.base, assumptions)
                    return fracNatPosExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
                except:
                    deduceInIntegers(exponent, assumptions)
                    deduceInComplexes([self.numerator.base, self.denominator.base], assumptions)
                    deduceNotZero(self.numerator.base, assumptions)
                    deduceNotZero(self.denominator.base, assumptions)
                    return fracIntExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
        raise Exception('Unable to combine exponents of this fraction')
        
    def cancel(self,operand, pull="left", assumptions=frozenset()):
        if self.numerator == self.denominator == operand:
            # x/x = 1
            from proveit.number.complex.theorems import fracCancelComplete
            deduceInComplexes(operand, assumptions)
            deduceNotZero(operand, assumptions)            
            return fracCancelComplete.specialize({x:operand}).checked(assumptions)
        
        if not isinstance(self.numerator,Multiply):
            from proveit.number.complex.theorems import fracCancel3
            newEq0 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(self.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            deduceInComplexes(operand, assumptions)
            deduceNotZero(operand, assumptions)            
            deduceInComplexes(newEq0.rhs.denominator.operands[1], assumptions)
            newEq1 = fracCancel3.specialize({x:operand,y:newEq0.rhs.denominator.operands[1]})
            return newEq0.applyTransitivity(newEq1)
            
        assert isinstance(self.numerator,Multiply)
        if isinstance(self.denominator,Multiply):
            from proveit.number.complex.theorems import fracCancel1
            newEq0 = self.numerator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(safeDummyVar(self),self.denominator),safeDummyVar(self)).checked(assumptions)
            newEq1 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(newEq0.rhs.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            deduceInComplexes(operand, assumptions)
            deduceNotZero(operand, assumptions)
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
            deduceNotZero(operand, assumptions)
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
            deduceInComplexes(self.numerator.operands, assumptions)
            deduceInComplexes(self.denominator, assumptions)
            return distributeFractionThroughSum.specialize({xEtc:self.numerator.operands, y:self.denominator})
        elif isinstance(self.numerator, Subtract):
            deduceInComplexes(self.numerator.operands, assumptions)
            deduceInComplexes(self.denominator, assumptions)
            return distributeFractionThroughSubtract.specialize({x:self.numerator.operands[0], y:self.numerator.operands[1], z:self.denominator})
        elif isinstance(self.numerator, Summation):
            # Should deduce in Complexes, but distributeThroughSummation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduceInComplexes(self.operands, assumptions)
            yEtcSub = self.numerator.indices
            Pop, Pop_sub = Operation(P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummyVar = safeDummyVar(self)            
            spec1 = distributeFractionThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, z:dummyVar})
            return spec1.deriveConclusion().specialize({dummyVar:self.denominator})
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

class Exponentiate(Operation, NumberOp):
    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        Operation.__init__(self,EXPONENTIATE, (base, exponent))
        self.base = base
        self.exponent = exponent

    def _closureTheorem(self, numberSet):
        import natural.theorems
        import real.theorems
        import complex.theorems
        from number import two
        if numberSet == NaturalsPos:
            return natural.theorems.powClosure
        elif numberSet == Reals:
            return real.theorems.powClosure
        elif numberSet == RealsPos:
            if self.exponent != two: # otherwise, use deduceInRealsPosDirectly(..)
                return real.theorems.powPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.powClosure
    
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive and return this exponential expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from number import zero, one
        from complex.theorems import powZeroEqOne, exponentiatedZero, exponentiatedOne
        from theorems import powOneUnchanged
        if self.exponent == zero:
            deduceInComplexes(self.base, assumptions)
            deduceNotZero(self.base, assumptions)
            return powZeroEqOne.specialize({a:self.base})
        elif self.exponent == one:
            return powOneUnchanged.specialize({a:self.base})
        elif self.base == zero:
            deduceInComplexes(self.exponent, assumptions)
            deduceNotZero(self.exponent, assumptions)
            return exponentiatedZero.specialize({x:self.exponent})
        elif self.base == one:
            deduceInComplexes(self.exponent, assumptions)
            return exponentiatedOne.specialize({x:self.exponent})
        else:
            raise ValueError('Only trivial simplification is implemented (zero or one for the base or exponent)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive this exponential expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def deduceInRealsPosDirectly(self, assumptions=frozenset()):
        import real.theorems
        from number import two
        if self.exponent == two:
            deduceInReals(self.base, assumptions)
            deduceNotZero(self.base, assumptions)
            return real.theorems.sqrdClosure.specialize({a:self.base}).checked(assumptions)
        # only treating certain special case(s) in this manner
        raise DeduceInNumberSetException(self, RealsPos, assumptions)

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
            if fence:
                return r'\left(' + formattedBase+'^{'+self.exponent.formatted(formatType, fence=False)+'}' + r'\right)'
            else:
                return formattedBase+'^{'+self.exponent.formatted(formatType, fence=False)+'}'
        elif formatType == STRING:
            if fence:
                return '(' + formattedBase+'^('+self.exponent.formatted(formatType, fence=False)+'))'
            else:
                return formattedBase+'^{'+self.exponent.formatted(formatType, fence=False)+'}'            
        else:
            print "BAD FORMAT TYPE"
            return None
    
    def distributeExponent(self, assumptions=frozenset()):
        from complex.theorems import fracIntExpRev, fracNatPosExpRev
        if isinstance(self.base, Fraction):
            exponent = self.exponent
            try:
                deduceInNaturalsPos(exponent, assumptions)
                deduceInComplexes([self.base.numerator, self.base.denominator], assumptions)
                deduceNotZero(self.base.denominator, assumptions)
                return fracNatPosExpRev.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
            except:
                deduceInIntegers(exponent, assumptions)
                deduceInComplexes([self.base.numerator, self.base.denominator], assumptions)
                deduceNotZero(self.base.numerator, assumptions)
                deduceNotZero(self.base.denominator, assumptions)
                return fracIntExpRev.specialize({n:exponent}).specialize({a:self.base.numerator, b:self.base.denominator})
        raise Exception('distributeExponent currently only implemented for a fraction base')
        
    def raiseExpFactor(self, expFactor, assumptions=frozenset()):
        from proveit.number.complex.theorems import intPowOfPow, intPowOfNegPow
        if isinstance(self.exponent, Neg):
            b_times_c = self.exponent.operand
            thm = intPowOfNegPow
        else:
            b_times_c = self.exponent
            thm = intPowOfPow
        if not hasattr(b_times_c, 'factor'):
            raise Exception('Exponent not factorable, may not raise the exponent factor.')
        factorEq = b_times_c.factor(expFactor, pull='right', groupRemainder=True, assumptions=assumptions)
        if factorEq.lhs != factorEq.rhs:
            # factor the exponent first, then raise this exponent factor
            factoredExpEq = factorEq.substitution(self)
            return factoredExpEq.applyTransitivity(factoredExpEq.rhs.raiseExpFactor(expFactor, assumptions=assumptions))
        nSub = b_times_c.operands[1]
        aSub = self.base
        bSub = b_times_c.operands[0]
        deduceNotZero(aSub, assumptions)
        deduceInIntegers(nSub, assumptions)
        deduceInComplexes([aSub, bSub], assumptions)
        return thm.specialize({n:nSub}).specialize({a:aSub, b:bSub}).deriveReversed()

    def lowerOuterPow(self, assumptions=frozenset()):
        from proveit.number.complex.theorems import intPowOfPow, intPowOfNegPow, negIntPowOfPow, negIntPowOfNegPow
        if not isinstance(self.base, Exponentiate):
            raise Exception('May only apply lowerOuterPow to nested Exponentiate operations')
        if isinstance(self.base.exponent, Neg) and isinstance(self.exponent, Neg):
            b_, n_ = self.base.exponent.operand, self.exponent.operand
            thm = negIntPowOfNegPow
        elif isinstance(self.base.exponent, Neg):
            b_, n_ = self.base.exponent.operand, self.exponent
            thm = intPowOfNegPow
        elif isinstance(self.exponent, Neg):
            b_, n_ = self.base.exponent, self.exponent.operand
            thm = negIntPowOfPow
        else:
            b_, n_ = self.base.exponent, self.exponent
            thm = intPowOfPow
        a_ = self.base.base
        deduceNotZero(self.base.base, assumptions)
        deduceInIntegers(n_, assumptions)
        deduceInComplexes([a_, b_], assumptions)
        return thm.specialize({n:n_}).specialize({a:a_, b:b_})
    
EXPONENTIATE = Literal(pkg, 'EXPONENTIATE', operationMaker = lambda operands : Exponentiate(*operands))

class Sqrt(Operation, NumberOp):
    def __init__(self, base):
        r'''
        Take the square root of the base.
        '''
        Operation.__init__(self, SQRT, (base))
        self.base = base
        
    def formatted(self, formatType, fence=False):
        formattedBase = self.base.formatted(formatType, fence=True)
        if formatType == LATEX:
            return r'\sqrt{' + formattedBase+'}'
        else:
            return Operation.formatted(self, formatType, fence)
    
    def distribute(self):
        '''
        Distribute the sqrt over a product.
        '''
        from real.theorems import sqrtOfProd
        if isinstance(self.base, Multiply):
            deduceInRealsPos(self.base.factors)
            return sqrtOfProd({xEtc:self.base.factors})

    def _closureTheorem(self, numberSet):
        import real.theorems
        import complex.theorems
        from number import two
        if numberSet == Reals:
            return real.theorems.sqrtClosure            
        elif numberSet == RealsPos:
            return real.theorems.sqrtPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.sqrtClosure


SQRT = Literal(pkg, 'SQRT', operationMaker = lambda operands : Sqrt(*operands))

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
        if numberSet == Reals:
            return real.theorems.summationClosure
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

    def simplification(self, assumptions=frozenset()):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a DiscreteContiguousSet where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from axioms import sumSingle
        if isinstance(self.domain, DiscreteContiguousSet) and self.domain.lowerBound == self.domain.upperBound:
            if len(self.instanceVars) == 1:
                deduceInIntegers(self.domain.lowerBound, assumptions)
                return sumSingle.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound})
        raise Exception("Summation simplification only implemented for a summation over a DiscreteContiguousSet of one instance variable where the upper and lower bound is the same")

    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a DiscreteContiguousSet where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def reduceGeomSum(self, assumptions=frozenset()):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        May need assumptions to proven prerequisite number set conditions.
        '''
        from proveit.number.complex.theorems import infGeomSum, finGeomSum
        from number import zero, infinity
        mVal = self.indices[0]
        
        try:
#            self.r = extractExpBase(self.summand)
            xVal = self.summand.base
        except:
            raise ValueError("Summand not an exponential!")
        if not isinstance(self.domain,DiscreteContiguousSet):
            raise ValueError("Not explicitly summing over DiscreteContiguousSet!")
        else:
            if self.domain.lowerBound == zero and self.domain.upperBound == infinity:
                #We're in the infinite geom sum domain!
                deduceInComplexes(xVal, assumptions)
                return infGeomSum.specialize({x:xVal, m:mVal})
            else:
                #We're in the finite geom sum domain!
                kVal = self.domain.lowerBound
                lVal = self.domain.upperBound
                deduceInIntegers(kVal, assumptions)
                deduceInIntegers(lVal, assumptions)
                deduceInComplexes(xVal, assumptions)
                return finGeomSum.specialize({x:xVal, m:mVal, k:kVal, l:lVal})
#        else:
#            print "Not a geometric sum!"

    def shift(self, shiftAmount, assumptions=frozenset()):
        '''
        Shift the summation indices by the shift amount, deducing and returning
        the equivalence of this summation with a index-shifted version.
        '''
        from integer.theorems import indexShift
        if len(self.indices) != 1 or not isinstance(self.domain, DiscreteContiguousSet):
            raise Exception('Summation shift only implemented for summations with one index over a DiscreteContiguousSet')
        fOp, fOpSub = Operation(f, self.index), self.summand
        deduceInIntegers(self.domain.lowerBound, assumptions)
        deduceInIntegers(self.domain.upperBound, assumptions)
        deduceInIntegers(shiftAmount, assumptions)
        return indexShift.specialize({fOp:fOpSub, x:self.index}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, c:shiftAmount})

    def join(self, secondSummation, assumptions=frozenset()):
        '''
        Join the "second summation" with "this" summation, deducing and returning
        the equivalence of these summations added with the joined summation.
        Both summation must be over DiscreteContiguousSets.
        The relation between the first summation upper bound, UB1, and the second
        summation lower bound, LB2 must be explicitly either UB1 = LB2-1 or LB2=UB1+1.
        '''
        from proveit.number.integer.theorems import sumSplitAfter, sumSplitBefore
        from proveit.number.common import one
        if not isinstance(self.domain, DiscreteContiguousSet) or not isinstance(secondSummation.domain, DiscreteContiguousSet):
            raise Exception('Summation joining only implemented for DiscreteContiguousSet domains')
        if self.summand != secondSummation.summand:
            raise Exception('Summation joining only allowed when the summands are the same')            
        if self.domain.upperBound == Subtract(secondSummation.domain.lowerBound, one):
            sumSplit = sumSplitBefore 
            splitIndex = secondSummation.domain.lowerBound
        elif secondSummation.domain.lowerBound == Add(self.domain.upperBound, one):
            sumSplit = sumSplitAfter
            splitIndex = self.domain.upperBound
        else:
            raise Exception('Summation joining only implemented when there is an explicit increment of one from the upper bound and the second summations lower bound')
        lowerBound, upperBound = self.domain.lowerBound, secondSummation.domain.upperBound
        deduceInIntegers(lowerBound, assumptions)
        deduceInIntegers(upperBound, assumptions)
        deduceInIntegers(splitIndex, assumptions)
        return sumSplit.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:lowerBound, b:splitIndex, c:upperBound, x:self.indices[0]}).deriveReversed()
        
    def split(self, splitIndex, side='after', assumptions=frozenset()):
        r'''
        Splits summation over one DiscreteContiguousSet {a ... c} into two summations.
        If side == 'after', it splits into a summation over {a ... splitIndex} plus
        a summation over {splitIndex+1 ... c}.  If side == 'before', it splits into
        a summation over {a ... splitIndex-1} plus a summation over {splitIndex ... c}.
        As special cases, splitIndex==a with side == 'after' splits off the first single
        term.  Also, splitIndex==c with side == 'before' splits off the last single term.
        r'''
        if not isinstance(self.domain, DiscreteContiguousSet) :
            raise Exception('Summation splitting only implemented for DiscreteContiguousSet domains')
        if side=='before' and self.domain.upperBound==splitIndex: return self.splitOffLast()
        if side=='after' and self.domain.lowerBound==splitIndex: return self.splitOffFirst()
        if isinstance(self.domain, DiscreteContiguousSet) and len(self.instanceVars) == 1:
            from proveit.number.integer.theorems import sumSplitAfter, sumSplitBefore
            sumSplit = sumSplitAfter if side == 'after' else sumSplitBefore
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            deduceInIntegers(splitIndex, assumptions)
            # Also needs lowerBound <= splitIndex and splitIndex < upperBound
            return sumSplit.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:splitIndex, c:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a DiscreteContiguousSet of one instance variable")


    def splitOffLast(self, assumptions=frozenset()):
        from proveit.number.integer.axioms import sumSplitLast
        if isinstance(self.domain, DiscreteContiguousSet) and len(self.instanceVars) == 1:
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            # Also needs lowerBound < upperBound
            return sumSplitLast.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a DiscreteContiguousSet of one instance variable")

    def splitOffFirst(self, assumptions=frozenset()):
        from proveit.number.integer.theorems import sumSplitFirst # only for associative summation
        if isinstance(self.domain, DiscreteContiguousSet) and len(self.instanceVars) == 1:
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            # Also needs lowerBound < upperBound
            return sumSplitFirst.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a DiscreteContiguousSet of one instance variable")

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
        # We need to deduce that theFactor is in Complexes and that all instances of Pop_sup are in Complexes.
        deduceInComplexes(factorOperands, assumptions=assumptions)
        deduceInComplexes(Pop_sub, assumptions=assumptions | {In(idx, self.domain) for idx in self.indices}).generalize(self.indices, domain=self.domain).checked(assumptions)
        # Now we specialize distributThroughSummationRev
        spec1 = distributeThroughSummationRev.specialize({Pop:Pop_sub, S:self.domain, yEtc:self.indices, xEtc:Etcetera(MultiVariable(xDummy)), zEtc:Etcetera(MultiVariable(zDummy))}).checked()
        eq.update(spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):xSub, Etcetera(MultiVariable(zDummy)):zSub}))
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
        import real.theorems
        import integer.theorems
        if numberSet == Complexes:
            return complex.theorems.negClosure
        elif numberSet == Reals:
            return real.theorems.negClosure
        elif numberSet == Integers:
            return integer.theorems.negClosure

    def _negativeTheorem(self):
        import real.theorems
        return real.theorems.negatedPositiveIsNegative

    def _positiveTheorem(self):
        import real.theorems
        return real.theorems.negatedNegativeIsPositive

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.negNotEqZero

    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return this Neg expression equated with the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from complex.theorems import negNeg, negZero
        from number import zero
        
        if isinstance(self.operand, Neg):
            deduceInComplexes(self.operand.operand, assumptions)
            return negNeg.specialize({a:self.operand.operand}).checked(assumptions)
        elif self.operand == zero:
            return negZero
        raise ValueError('Only trivial simplification is implemented (double negation or negating zero)')
        
    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    
    def formatted(self, formatType, fence=False):
        outStr = ''
        if fence: outStr += r'\left(' if formatType == LATEX else r'('
        outStr += ('-'+self.operand.formatted(formatType, fence=True))
        if fence: outStr += r'\right)' if formatType == LATEX else r')'
        return outStr

    def distribute(self, assumptions=frozenset()):
        '''
        Distribute negation through a sum.
        '''
        from complex.theorems import distributeNegThroughSum, distributeNegThroughSubtract
        if isinstance(self.operand, Add):
            deduceInComplexes(self.operand.operands, assumptions)
            # distribute the negation over the sum
            eqn = Equation(distributeNegThroughSum.specialize({xEtc:self.operand.operands}))
            # try to simplify each term
            expr = eqn.eqExpr.rhs
            dummyVar = self.safeDummyVar()
            negatedTerms = [term for term in expr.operands]
            for k, negatedTerm in enumerate(negatedTerms):
                try:
                    negTermSimplification = negatedTerm.simplification(assumptions)
                    eqn.update(negTermSimplification.substitution(Add(*(expr.terms[:k] + [dummyVar] + expr.terms[k+1:])), dummyVar)).checked(assumptions)
                    expr = eqn.eqExpr.rhs
                except:
                    pass # skip over                     
            return eqn.eqExpr.checked(assumptions)
        elif isinstance(self.operand, Subtract):
            deduceInComplexes(self.operand.operands, assumptions)
            return distributeNegThroughSubtract.specialize({x:self.operand.operands[0], y:self.operand.operands[1]}).checked(assumptions)
        else:
            raise Exception('Only negation distribution through a sum or subtract is implemented')

    def factor(self,operand,pull="left", groupFactor=None, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a negated expression, pulling it either to the "left" or "right".
        groupFactor and groupRemainder are not relevant but kept for compatibility with 
        other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
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

class Integrate(OperationOverInstances, NumberOp):
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
        self.index = self.instanceVars[0]
        self.integrand = self.instanceExpr

    def _closureTheorem(self, numberSet):
        import real.theorems
        #import complex.theorems
        if numberSet == Reals:
            return real.theorems.integrationClosure
        #if numberSet == Complexes:
        #    return complex.theorems.integrationClosure

        
    def formatted(self, formatType, fence=False):
#        if isinstance(self.domain,IntervalOO) or isinstance(self.domain,IntervalOC) or isinstance(self.domain,IntervalCO) or isinstance(self.domain,IntervalOO):
        if isinstance(self.domain,IntervalCC):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            return self.operator.formatted(formatType)+r'_{'+lower+r'}'+r'^{'+upper+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)
#        elif self.domain

        return self.operator.formatted(formatType)+r'_{'+self.domain.formatted(formatType)+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)


def integrateMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return Integrate(params['instanceVars'],params['instanceExpr'],params['domain'],params['conditions'])


INTEGRATE = Literal(pkg, "INTEGRATE", {STRING: r'Integrate', LATEX: r'\int'}, operationMaker = integrateMaker)
