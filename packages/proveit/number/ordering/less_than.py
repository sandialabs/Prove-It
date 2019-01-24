from proveit import Literal, USE_DEFAULTS, asExpression
from proveit.logic import Equals
from .ordering_relation import OrderingRelation, OrderingSequence
from proveit._common_ import a, b, c, x, y, z

class LesserRelation(OrderingRelation):
    def __init__(self, operator, lhs, rhs):
        OrderingRelation.__init__(self, operator, lhs, rhs)

    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.lhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.rhs
    
    @staticmethod
    def WeakRelationClass():
        return LessEq # <= is weaker than <

    @staticmethod
    def StrongRelationClass():
        return Less # < is stronger than <=                

    @staticmethod
    def SequenceClass():
        return LesserSequence

class LesserSequence(OrderingSequence):
    def __init__(self, operators, operands):
        OrderingSequence.__init__(self, operators, operands)
        # Containment in the {<, <=, =} set is relevant when dealing with a LesserSequence,
        # so let's go ahead and import these unquantified theorems.
        try:
            from ._theorems_ import less__in__less_eq_relations, less_eq__in__less_eq_relations, eq__in__less_eq_relations
        except:
            # may fail before the relevent _theorems_ have been generated
            pass # and that's okay    

    @staticmethod
    def RelationClass():
        return LesserRelation                

class Less(LesserRelation):
    # operator of the Less operation.
    _operator_ = Literal(stringFormat='<', context=__file__)
    
    # map left-hand-sides to "<" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to "<" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()  
    
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at bigger than first.
        '''
        OrderingRelation.__init__(self, Less._operator_,lhs,rhs)
                    
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .greater_than import GreaterThan
        return GreaterThan(self.rhs, self.lhs)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x < y derive y > x.
        '''
        from ._theorems_ import reverseLess
        return reverseLess.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
                
    def deduceInBooleans(self, assumptions=frozenset()):
        from ._theorems_ import lessThanInBools
        return lessThanInBools.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)

    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a < b to a <= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from ._theorems_ import relaxLessThan
        return relaxLessThan.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)
        
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x<y expression 
        and something of the form y<z, y<=z, z>y, z>=y, or y=z to
        obtain x<z.
        '''
        from ._axioms_ import transitivityLessLess
        from ._theorems_ import transitivityLessLessEq
        from .greater_than import Greater, GreaterEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return OrderingRelation.applyTransitivity(self, other, assumptions) # handles this special case
        if isinstance(other,Greater) or isinstance(other,GreaterEq):
            other = other.deriveReversed(assumptions)
        elif other.lhs == self.rhs:
            if isinstance(other,Less):
                return transitivityLessLess.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,LessEq):
                return transitivityLessLessEq.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Less):
                return transitivityLessLess.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,LessEq):
                return transitivityLessLessEq.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a < b`, derive and return :math:`-a > -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from ._theorems_ import negatedLessThan
        return negatedLessThan.specialize({a:self.lhs, b:self.rhs})
        
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a < b`, derive and return :math:`a + c < b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from ._theorems_ import lessThanAddRight, lessThanAddLeft, lessThanSubtract
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}, assumptions=assumptions)
            else:
            '''
            return lessThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return lessThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))
    
class LessEq(LesserRelation):
    # operator of the LessEq operation.
    _operator_ = Literal(stringFormat='<=', latexFormat=r'\leq', context=__file__)
    
    # map left-hand-sides to "<=" KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to "<=" KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()  
            
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at least as big as first.
        '''
        LesserRelation.__init__(self, LessEq._operator_,lhs,rhs)
            
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .greater_than import GreaterThanEquals
        return GreaterThanEquals(self.rhs, self.lhs)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From, e.g., x <= y derive y >= x etc.
        '''
        from ._theorems_ import reverseLessEq
        return reverseLessEq.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)

    def deduceInBooleans(self, assumptions=frozenset()):
        from ._theorems_ import lessThanEqualsInBools
        return lessThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)
    
    def unfold(self, assumptions=frozenset()):
        from ._axioms_ import lessThanEqualsDef
        return lessThanEqualsDef.specialize({x:self.lhs, y:self.rhs})
    
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x<=y expression 
        and something of the form y<z, y<=z, z>y, z>=y, or y=z to
        obtain x<z or x<=z as appropriate.  In the special case
        of x<=y and y<=x (or x>=y), derive x=z.
        '''
        from ._theorems_ import transitivityLessEqLess, transitivityLessEqLessEq, symmetricLessEq
        from .greater_than import Greater, GreaterEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return OrderingRelation.applyTransitivity(self, other, assumptions) # handles this special case
        if isinstance(other,Greater) or isinstance(other,GreaterEq):
            other = other.deriveReversed(assumptions)
        if other.lhs == self.rhs and other.rhs == self.lhs:
            # x >= y and y >= x implies that x=y
            return symmetricLessEq.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
        elif other.lhs == self.rhs:
            if isinstance(other,Less):
                return transitivityLessEqLess.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,LessEq):
                return transitivityLessEqLessEq.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Less):
                return transitivityLessEqLess.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,LessEq):
                return transitivityLessEqLessEq.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \leq b`, derive and return :math:`-a \geq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from ._theorems_ import negatedLessThanEquals
        return negatedLessThanEquals.specialize({a:self.lhs, b:self.rhs})
    
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \leq b`, derive and return :math:`a + c \leq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from ._theorems_ import lessThanEqualsAddRight, lessThanEqualsAddLeft, lessThanEqualsSubtract
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}, assumptions=assumptions)
            else:
            '''
            return lessThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return lessThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))
        
def LessSeq(*operands):
    return LesserSequence([Less._operator_]*(len(operands)-1), operands)

def LessEqSeq(*operands):
    return LesserSequence([LessEq._operator_]*(len(operands)-1), operands)
