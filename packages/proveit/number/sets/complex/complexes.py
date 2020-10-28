import proveit
from proveit import USE_DEFAULTS
from proveit._common_ import a, x, y
from proveit.number.sets.number_set import NumberSet

class ComplexSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Complexes', r'\mathbb{C}', context=__file__)

    def deduceInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from .theorems import inComplexesIsBool
        return inComplexesIsBool.specialize({a:element}, assumptions)
    
    def deduceNotInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from .theorems import notInComplexesIsBool
        return notInComplexesIsBool.specialize({a:element}, assumptions)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInComplexesInBool
        from proveit._common_ import x
        return xInComplexesInBool.specialize({x:member}, assumptions=assumptions)
    
    @staticmethod
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of an Equals relation by the 'multiplier' 
        on the left.
        '''        
        from proveit.logic import Equals
        from proveit.number.multiplication._theorems_ import left_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq.instantiate(
                {a:multiplier, x:relation.lhs, y:relation.rhs}, 
                assumptions=assumptions)

    @staticmethod
    def left_mult_both_sides_of_notequals(relation, multiplier,
                                          assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of a NonEquals relation by the 'multiplier' 
        on the left.
        '''        
        from proveit.logic import NotEquals
        from proveit.number.multiplication._theorems_ import left_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq.instantiate(
                {a:multiplier, x:relation.lhs, y:relation.rhs}, 
                assumptions=assumptions)

    @staticmethod
    def right_mult_both_sides_of_equals(relation, multiplier, 
                                     assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of an Equals relation by the 'multiplier' 
        on the right.
        '''
        from proveit.logic import Equals        
        from proveit.number.multiplication._theorems_ import right_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq.instantiate(
                {a:multiplier, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)
                
    @staticmethod
    def right_mult_both_sides_of_notequals(relation, multiplier, 
                                        assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of a NotEquals relation by the 'multiplier' 
        on the right.
        '''
        from proveit.logic import NotEquals        
        from proveit.number.multiplication._theorems_ import right_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq.instantiate(
                {a:multiplier, x:relation.lhs, y:relation.rhs}, 
                assumptions=assumptions)
    
    @staticmethod
    def divide_both_sides_of_equals(relation, divisor, 
                                    assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.logic import Equals
        from proveit.number.division._theorems_ import div_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq.instantiate(
                {a:divisor, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)

    @staticmethod
    def divide_both_sides_of_notequals(relation, divisor, 
                                       assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.logic import NotEquals
        from proveit.number.division._theorems_ import div_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq.instantiate(
                {a:divisor, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)
    
    @staticmethod
    def left_add_both_sides_of_equals(relation, addend, 
                                      assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.number.addition._theorems_ import left_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq.instantiate(
                {a:addend, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)
    
    @staticmethod
    def left_add_both_sides_of_notequals(relation, addend, 
                                         assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import NotEquals
        from proveit.number.addition._theorems_ import left_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq.instantiate(
                {a:addend, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)    
    
    
    @staticmethod
    def right_add_both_sides_of_equals(relation, addend, 
                                       assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import Equals
        from proveit.number.addition._theorems_ import right_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq.instantiate(
                {a:addend, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)

    @staticmethod
    def right_add_both_sides_of_notequals(relation, addend, 
                                          assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import NotEquals
        from proveit.number.addition._theorems_ import right_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq.instantiate(
                {a:addend, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)
    
    @staticmethod
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.logic import Equals        
        from proveit.number.exponentiation._theorems_ import exp_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq.instantiate(
                {a:exponent, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)

    @staticmethod
    def exponentiate_both_sides_of_notequals(relation, exponent,
                                          assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'exponent'.
        '''
        from proveit.logic import NotEquals        
        from proveit.number.exponentiation._theorems_ import exp_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return exp_neq.instantiate(
                {a:exponent, x:relation.lhs, y:relation.rhs},
                assumptions=assumptions)
                
    @staticmethod
    def square_both_sides_of_equals(relation,
                                    assumptions=USE_DEFAULTS):
        '''
        Square both sides of the Equals relation.
        '''
        from proveit.number import two
        return ComplexSet.exponentiate_both_sides_of_equals(relation,
                two, assumptions=assumptions)

    @staticmethod
    def square_both_sides_of_notequals(relation,
                                       assumptions=USE_DEFAULTS):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.number import two
        return ComplexSet.exponentiate_both_sides_of_notequals(relation,
                two, assumptions=assumptions)

    @staticmethod
    def square_root_both_sides_of_equals(relation, assumptions=USE_DEFAULTS):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.number import frac, one, two
        new_rel = ComplexSet.exponentiate_both_sides_of_equals(relation,
                frac(one, two), assumptions=assumptions)
        new_rel = new_rel.innerExpr().lhs.withStyles(exponent='radical')
        new_rel = new_rel.innerExpr().rhs.withStyles(exponent='radical')
        return new_rel
    
    @staticmethod
    def square_root_both_sides_of_notequals(relation, 
                                            assumptions=USE_DEFAULTS):
        '''
        Take the square root of both sides of the NotEquals relation.
        '''
        from proveit.number import frac, one, two
        new_rel = ComplexSet.exponentiate_both_sides_of_notequals(relation,
                frac(one, two), assumptions=assumptions)
        new_rel = new_rel.innerExpr().lhs.withStyles(exponent='radical')
        new_rel = new_rel.innerExpr().rhs.withStyles(exponent='radical')
        return new_rel
    
    
# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from ._theorems_ import realsInComplexes, realsPosInComplexes, realsNegInComplexes, intsInComplexes, natsInComplexes

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import realsInComplexes, intsInComplexes, natsInComplexes
    
