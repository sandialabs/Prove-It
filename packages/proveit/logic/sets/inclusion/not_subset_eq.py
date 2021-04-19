from proveit import (as_expression, Literal, Operation, safe_dummy_var,
                     USE_DEFAULTS)
from proveit import A, B, C, x
from proveit import f, S
from proveit.relation import Relation

class NotSubsetEq(Relation):
    # operator of the NotSubsetEq operation
    _operator_ = Literal(string_format='not_subset_eq', 
                         latex_format=r'\nsubseteq',
                         theory=__file__)

    def __init__(self, A, B, *, styles=None):
        '''
        Create the expression for (A not_subset_eq B)
        '''
        Operation.__init__(self, NotSubsetEq._operator_, (A, B),
                           styles=styles)

    @staticmethod
    def reversed_operator_str(format_type):
        '''
        Reversing not_subset_eq gives not_superset_eq.
        '''
        return r'\nsupseteq' if format_type == 'latex' else 'not_superset_eq'

    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'not_superset_eq' function if it is reversed.
            return 'not_superset_eq'
        # Use the default.
        return Operation.remake_constructor(self)
    
    def side_effects(self, judgment):
        # unfold as an automatic side-effect
        yield self.unfold

    def conclude(self, assumptions):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsubseteq B, derive and return not(supseteq(A, B)).
        '''
        from . import unfold_not_subset_eq
        unfolded = unfold_not_subset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        return unfolded.inner_expr().operand.with_mimicked_style(self)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from . import fold_not_subset_eq
        concluded = fold_not_subset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        return concluded.with_matching_style(self)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotSubsetEq statement is in the
        Boolean set.
        '''
        from . import not_subset_eq_is_bool
        is_bool_stmt = not_subset_eq_is_bool.instantiate(
            {A: self.operands[0], B: self.operands[1]})
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

def not_superset_eq(A, B):
    '''
    Return the expression representing (A not_superset_eq B), internally
    represented as (B not_subset_eq A) but with a style that reverses
    the direction.
    '''
    return NotSubsetEq(B, A).with_styles(direction='reversed')
