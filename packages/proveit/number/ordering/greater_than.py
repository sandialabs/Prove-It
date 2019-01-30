from proveit import Literal, USE_DEFAULTS, asExpression
from proveit.logic import Equals
from .ordering_relation import OrderingRelation, OrderingSequence
from proveit._common_ import a, b, c, x, y, z

class GreaterRelation(OrderingRelation):
    def __init__(self, operator, lhs, rhs):
        OrderingRelation.__init__(self, operator, lhs, rhs)
    
    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.rhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.lhs
    
    @staticmethod
    def WeakRelationClass():
        return GreaterEq # >= is weaker than >

    @staticmethod
    def StrongRelationClass():
        return Greater # > is stronger than >=                

    @staticmethod
    def SequenceClass():
        return GreaterSequence

class GreaterSequence(OrderingSequence):
    def __init__(self, operators, operands):
        OrderingSequence.__init__(self, operators, operands)
        # Containment in the {>, >=, =} set is relevant when dealing with a GreaterSequence,
        # so let's go ahead and import these unquantified theorems.
        try:
            from ._theorems_ import greater__in__greater_eq_relations, greater_eq__in__greater_eq_relations, eq__in__greater_eq_relations
        except:
            # may fail before the relevent _theorems_ have been generated
            pass # and that's okay    
    @staticmethod
    def RelationClass():
        return GreaterRelation  

class Greater(GreaterRelation):
    # operator of the Greater operation.
    _operator_ = Literal(stringFormat='>', context=__file__)
    
    # map left-hand-sides to ">" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to ">" KnownTruths 
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()   
            
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, Greater._operator_,lhs,rhs)
        
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .less_than import LessThan
        return LessThan(self.rhs, self.lhs)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From, x > y derive y < x.
        '''
        from ._theorems_ import reverseGreater
        return reverseGreater.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
                    
    def deduceInBooleans(self, assumptions=frozenset()):
        from ._theorems_ import greaterThanInBools
        return greaterThanInBools.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)
    
    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a > b to a >= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from ._theorems_ import relaxGreaterThan
        return relaxGreaterThan.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)
        
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        from ._theorems_ import transitivityGreaterGreater, transitivityGreaterGreaterEq
        from .less_than import Less, LessEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return OrderingRelation.applyTransitivity(self, other, assumptions) # handles this special case
        if isinstance(other,Less) or isinstance(other,LessEq):
            other = other.deriveReversed(assumptions)
        if other.lhs == self.rhs:
            if isinstance(other,Greater):
                return transitivityGreaterGreater.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterGreaterEq.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Greater):
                return transitivityGreaterGreater.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterGreaterEq.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a > b`, derive and return :math:`-a < -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from ._theorems_ import negatedGreaterThan
        return negatedGreaterThan.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a > b`, derive and return :math:`a + c > b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from ._theorems_ import greaterThanAddRight, greaterThanAddLeft, greaterThanSubtract
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}, assumptions=assumptions)
            else:
            '''
            return greaterThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return greaterThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

class GreaterEq(GreaterRelation):
    # operator of the GreaterEq operation.
    _operator_ = Literal(stringFormat='>=', latexFormat=r'\geq', context=__file__)
    
    # map left-hand-sides to ">=" KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to ">=" KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()   
        
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        GreaterRelation.__init__(self, GreaterEq._operator_,lhs,rhs)
    
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .less_than import LessThanEquals
        return LessThanEquals(self.rhs, self.lhs)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From, x >= y derive y <= x.
        '''
        from ._theorems_ import reverseGreaterEq
        return reverseGreaterEq.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
                            
    def deduceInBooleans(self, assumptions=frozenset()):
        from ._theorems_ import greaterThanEqualsInBools
        return greaterThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}, assumptions=assumptions)

    def unfold(self, assumptions=frozenset()):
        from ._axioms_ import greaterThanEqualsDef
        return greaterThanEqualsDef.specialize({x:self.lhs, y:self.rhs})

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x>=y expression 
        and something of the form y>z, y>=z, z<y, z<=y, or y=z to
        obtain x>z or x>=z as appropriate.  In the special case
        of x>=y and y>=x (or x<=y), derive x=z.
        '''
        from ._theorems_ import transitivityGreaterEqGreater, transitivityGreaterEqGreaterEq, symmetricGreaterEq
        from .less_than import Less, LessEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return OrderingRelation.applyTransitivity(self, other, assumptions) # handles this special case
        if isinstance(other,Less) or isinstance(other,LessEq):
            other = other.deriveReversed(assumptions)
        if other.lhs == self.rhs and other.rhs == self.lhs:
            # x >= y and y >= x implies that x=y
            return symmetricGreaterEq.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
        elif other.lhs == self.rhs:
            if isinstance(other,Greater):
                return transitivityGreaterEqGreater.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterEqGreaterEq.specialize({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Greater):
                return transitivityGreaterEqGreater.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterEqGreaterEq.specialize({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \geq b`, derive and return :math:`-a \leq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from ._theorems_ import negatedGreaterThanEquals
        return negatedGreaterThanEquals.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \geq b`, derive and return :math:`a + c \geq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from ._theorems_ import greaterThanEqualsAddRight, greaterThanEqualsAddLeft, greaterThanEqualsSubtract
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}, assumptions=assumptions)
            else:
            '''
            return greaterThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return greaterThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

def GreaterSeq(*operands):
    return GreaterSequence([Greater._operator_]*(len(operands)-1), operands)

def GreaterEqSeq(*operands):
    return GreaterSequence([GreaterEq._operator_]*(len(operands)-1), operands)

def greaterSequence(operators, operands):
    '''
    Create a GreaterSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    if len(operators)+1 != len(operands):
        raise ValueError("Expecting one more operand than operators")
    if operators==0:
        return operands[0]
    if operators==1:
        if operators[0]==Greater._operator_:
            return Greater(*operands)
        elif operators[0]==Equals._operator_:
            return Equals(*operands)
    return GreaterSequence(operators, operands)

        