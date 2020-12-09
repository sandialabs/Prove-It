from proveit import Literal, USE_DEFAULTS, asExpression
from proveit.logic import Equals
from .ordering_relation import OrderingRelation, OrderingSequence, makeSequenceOrRelation
from proveit._common_ import a, b, c, d, x, y, z

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
    _operator_ = Literal(stringFormat='>', theory=__file__)
    
    # map left-hand-sides to ">" Judgments
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to ">" Judgments 
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()   
            
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, Greater._operator_,lhs,rhs)
        
    def conclude(self, assumptions):
        from ._theorems_ import positiveIfInRealPos
        from proveit.numbers import zero
        if self.rhs == zero:
            positiveIfInRealPos.instantiate({a:self.lhs},
                                             assumptions=assumptions)
        return GreaterRelation.conclude(self, assumptions)
    
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
        return reverseGreater.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)
                    
    def deduceInBool(self, assumptions=frozenset()):
        from ._theorems_ import greaterThanInBool
        return greaterThanInBool.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)
    
    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a > b to a >= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Real.
        '''
        from ._theorems_ import relaxGreater
        return relaxGreater.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)

    def deduceIncAdd(self, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19
        if self.lhs is addition, deduce strictly increasing addition
        '''
        from proveit.numbers import Add

        if isinstance(self.lhs,Add):
            return self.lhs.deduceStrictIncAdd(self.rhs, assumptions)
        else:
            raise ValueError("expected self.lhs to be addition")

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
                return transitivityGreaterGreater.instantiate({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterGreaterEq.instantiate({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Greater):
                return transitivityGreaterGreater.instantiate({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterGreaterEq.instantiate({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a > b`, derive and return :math:`-a < -b`.
        Assumptions may be required to prove that a, and b are in Real.        
        '''
        from ._theorems_ import negatedGreaterThan
        return negatedGreaterThan.instantiate({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=USE_DEFAULTS):
        r'''
        From a > b, derive and return a + c > b + c 
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in 
        Real.
        '''
        from ._theorems_ import greaterShiftAddRight, greaterShiftAddLeft
        if addendSide == 'right':
            return greaterShiftAddRight.instantiate({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return greaterShiftAddLeft.instantiate({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

    def addLeft(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a + c > b given c >= 0 (and a, b, c 
        are all Real) where c is the given 'addend'.
        '''
        from ._theorems_ import greaterAddLeft
        return greaterAddLeft.instantiate({a:self.lhs, b:self.rhs, c:addend},
                                          assumptions=assumptions)

    def addRight(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a > b + c given 0 >= c (and a, b, c 
        are all Real) where c is the given 'addend'.
        '''
        from ._theorems_ import greaterAddRight
        return greaterAddRight.instantiate({a:self.lhs, b:self.rhs, c:addend},
                                           assumptions=assumptions)                
                                        
    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a + c > b + d given c > d 
        (and a, b, c, d are all Real).  c and d are determined from the
        given 'relation'.
        '''
        from .less_than import Less, LessEq
        from ._theorems_ import greaterAddBoth
        if isinstance(relation, Greater) or isinstance(relation, GreaterEq):
            c_val = relation.lhs
            d_val = relation.rhs
        elif isinstance(relation, Less) or isinstance(relation, LessEq):
            c_val = relation.rhs
            d_val = relation.lhs
        else:
            raise ValueError("Greater.add 'relation' must be of type Less, "
                               "LessEq, Greater, or GreaterEq, not %s"
                               %str(relation.__class__))
        return greaterAddBoth.instantiate({a:self.lhs, b:self.rhs, c:c_val,
                                           d:d_val},
                                          assumptions=assumptions)

    def concludeViaEquality(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import relaxEqualToGreaterEq
        return relaxEqualToGreaterEq.instantiate(
            {x: self.operands[0], y:self.operands[1]},
            assumptions=assumptions) 


class GreaterEq(GreaterRelation):
    # operator of the GreaterEq operation.
    _operator_ = Literal(stringFormat='>=', latexFormat=r'\geq', theory=__file__)
    
    # map left-hand-sides to ">=" Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to ">=" Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()   
        
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        GreaterRelation.__init__(self, GreaterEq._operator_,lhs,rhs)
    
    def conclude(self, assumptions):
        # See if the right side is the left side plus something 
        # positive added to it.
        from proveit.numbers import zero
        if self.rhs == zero:
            from ._theorems_ import nonNegIfInRealNonNeg
            return nonNegIfInRealNonNeg.instantiate(
                    {a:self.lhs}, assumptions=assumptions)
        return GreaterRelation.conclude(self, assumptions)
    
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
        return reverseGreaterEq.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)
                            
    def deduceInBool(self, assumptions=frozenset()):
        from ._theorems_ import greaterThanEqualsInBool
        return greaterThanEqualsInBool.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)

    def unfold(self, assumptions=frozenset()):
        from ._axioms_ import greaterThanEqualsDef
        return greaterThanEqualsDef.instantiate({x:self.lhs, y:self.rhs})

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
            return symmetricGreaterEq.instantiate({x:self.lhs, y:self.rhs}, assumptions=assumptions)
        elif other.lhs == self.rhs:
            if isinstance(other,Greater):
                return transitivityGreaterEqGreater.instantiate({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterEqGreaterEq.instantiate({x:self.lhs, y:self.rhs, z:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Greater):
                return transitivityGreaterEqGreater.instantiate({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
            elif isinstance(other,GreaterEq):
                return transitivityGreaterEqGreaterEq.instantiate({x:self.lhs, y:self.rhs, z:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))        
    
    """
    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \geq b`, derive and return :math:`-a \leq -b`.
        Assumptions may be required to prove that a, and b are in Real.        
        '''
        from ._theorems_ import negatedGreaterThanEquals
        return negatedGreaterThanEquals.instantiate({a:self.lhs, b:self.rhs})
    """

    def deriveShifted(self, addend, addendSide='right', assumptions=USE_DEFAULTS):
        r'''
        From a >= b, derive and return a + c >= b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in 
        Real.
        '''
        from ._theorems_ import greaterEqShiftAddRight, greaterEqShiftAddLeft
        if addendSide == 'right':
            return greaterEqShiftAddRight.instantiate({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        elif addendSide == 'left':
            return greaterEqShiftAddLeft.instantiate({a:self.lhs, b:self.rhs, c:addend}, assumptions=assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

    def addLeft(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a + c >= b given c >= 0 (and a, b, c 
        are all Real) where c is the given 'addend'.
        '''
        from ._theorems_ import greaterEqAddLeft
        return greaterEqAddLeft.instantiate({a:self.lhs, b:self.rhs, c:addend},
                                          assumptions=assumptions)

    def addRight(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a >= b + c given 0 >= c (and a, b, c 
        are all Real) where c is the given 'addend'.
        '''
        from ._theorems_ import greaterEqAddRight
        return greaterEqAddRight.instantiate({a:self.lhs, b:self.rhs, c:addend},
                                           assumptions=assumptions)                
                                        
    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a + c >= b + d given c >= d 
        (and a, b, c, d are all Real).  c and d are determined from the
        given 'relation'.
        '''
        from .less_than import Less, LessEq
        from ._theorems_ import greaterEqAddBoth
        if isinstance(relation, Greater) or isinstance(relation, GreaterEq):
            c_val = relation.lhs
            d_val = relation.rhs
        elif isinstance(relation, Less) or isinstance(relation, LessEq):
            c_val = relation.rhs
            d_val = relation.lhs
        else:
            raise ValueError("Greater.add 'relation' must be of type Less, "
                               "LessEq, Greater, or GreaterEq, not %s"
                               %str(relation.__class__))
        return greaterEqAddBoth.instantiate({a:self.lhs, b:self.rhs, c:c_val,
                                             d:d_val},
                                            assumptions=assumptions)

def GreaterOnlySeq(*operands):
    return GreaterSequence([Greater._operator_]*(len(operands)-1), operands)

def GreaterEqOnlySeq(*operands):
    return GreaterSequence([GreaterEq._operator_]*(len(operands)-1), operands)

def greaterSequence(operators, operands):
    '''
    Create a GreaterSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return makeSequenceOrRelation(GreaterSequence, operators, operands)
