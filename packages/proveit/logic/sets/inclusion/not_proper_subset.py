from proveit import (as_expression, Literal, Operation, safe_dummy_var,
                     USE_DEFAULTS)
from proveit import A, B, C, x
from proveit import f, S
from proveit.relation import Relation

class NotProperSubset(Relation):
    # operator for the NotProperSubset operation
    _operator_ = Literal(string_format='not_proper_subset',
                         latex_format=r'\not\subset',
                         theory=__file__)

    def __init__(self, A, B):
        '''
        Create the expression for (A not_proper_subset B)
        '''
        Operation.__init__(
            self, NotProperSubset._operator_, (A, B))
        # Need 'direction' style

    @staticmethod
    def reversed_operator_str(format_type):
        '''
        Reversing not_proper_subset gives not_proper_subset.
        '''
        return r'\not\supset' if format_type == 'latex' else 'not_proper_subset'
    
    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'not_proper_superset' function if it 
            # is reversed.
            return 'not_proper_superset'
        # Use the default.
        return Operation.remake_constructor(self)
    
    def side_effects(self, judgment):
        yield self.unfold

    def conclude(self, assumptions=USE_DEFAULTS):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A not_proper_subset B, derive and return
        not(propersubset(A, B)).
        '''
        from . import unfold_not_proper_subset
        unfolded = unfold_not_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, 
            assumptions=assumptions)
        return unfolded.inner_expr().operand.with_mimicked_style(self)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A not_proper_subset B, from the
        unfolded version, not(A propersubset B).
        '''
        from . import fold_not_proper_subset
        concluded = fold_not_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, 
            assumptions=assumptions)
        return concluded.with_matching_style(self)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotProperSubset statement is in the
        Boolean set.
        '''
        from . import not_proper_subset_is_bool
        is_bool_stmt = not_proper_subset_is_bool.instantiate(
            {A: self.operands[0], B: self.operands[1]})
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

def not_proper_superset(A, B):
    '''
    Return the expression representing (A not_proper_superset B), 
    internally represented as (B not_proper_subset A) but with a style 
    that reverses the direction.
    '''
    return NotProperSubset(B, A).with_styles(direction='reversed')
