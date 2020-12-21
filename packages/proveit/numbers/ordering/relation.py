from .ordering_relation import OrderingRelation
from proveit.logic import Equals

class Relation:
    '''
    Relation wraps an OrderingRelation (LessThan,LessThanEquals,GreaterThan, or GreaterThanEquals)
    or Equals expression, A[rel]B, that can be updated via
    new relations that involve A or B, deriving each new relation from
    the previous relation.
    '''
    def __init__(self, rel_expr):
        '''
        Initialize the Inequality with an OrderingRelation expression.
        '''
        if not isinstance(rel_expr,OrderingRelation) and not isinstance(rel_expr,Equals):
            raise ValueError('Relation must be initialized with an OrderingRelation or Equals expression')
        self.rel_expr = rel_expr

    def update(self, next_rel_expr):
        '''
        Update the old equation via next_eq_expr to a new equation that is
        derived from the old equation and next_eq_expr.  This new equation
        is then stored as "the equation" and returned.  For example, if 
        the old equation is A=B and next_eq_expr is B=C, then update derives, 
        stores (ready for the next update), and returns A=C.
        '''
        if not isinstance(next_rel_expr, OrderingRelation) and not isinstance(next_rel_expr, Equals):
            raise ValueError('Relation may updated only with an OrderingRelation or Equals expression')
        if isinstance(self.rel_expr, OrderingRelation) or (isinstance(self.rel_expr, Equals) and isinstance(next_rel_expr, Equals)):
            self.rel_expr = self.rel_expr.apply_transitivity(next_rel_expr).checked({self.rel_expr, next_rel_expr})
        else:#Updating an equals with an inequality!
            self.rel_expr = next_rel_expr.apply_transitivity(self.rel_expr).checked({self.rel_expr,next_rel_expr})#.derive_reversed()
        return self.rel_expr

    
    def proven(self, assumptions=frozenset()):
        '''
        Forwards this proven "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.ineq_expr.proven(assumptions)
        return self

    def qed(self, filename):
        '''
        Forwards this qed "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.ineq_expr.qed(filename)
        return self.eq_expr
