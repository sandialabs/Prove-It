from ordering_relation import OrderingRelation
from proveit.logic import Equals

class Relation:
    '''
    Relation wraps an OrderingRelation (LessThan,LessThanEquals,GreaterThan, or GreaterThanEquals)
    or Equals expression, A[rel]B, that can be updated via
    new relations that involve A or B, deriving each new relation from
    the previous relation.
    '''
    def __init__(self, relExpr):
        '''
        Initialize the Inequality with an OrderingRelation expression.
        '''
        if not isinstance(relExpr,OrderingRelation) and not isinstance(relExpr,Equals):
            raise ValueError('Relation must be initialized with an OrderingRelation or Equals expression')
        self.relExpr = relExpr

    def update(self, nextRelExpr):
        '''
        Update the old equation via nextEqExpr to a new equation that is
        derived from the old equation and nextEqExpr.  This new equation
        is then stored as "the equation" and returned.  For example, if 
        the old equation is A=B and nextEqExpr is B=C, then update derives, 
        stores (ready for the next update), and returns A=C.
        '''
        if not isinstance(nextRelExpr, OrderingRelation) and not isinstance(nextRelExpr, Equals):
            raise ValueError('Relation may updated only with an OrderingRelation or Equals expression')
        if isinstance(self.relExpr, OrderingRelation) or (isinstance(self.relExpr, Equals) and isinstance(nextRelExpr, Equals)):
            self.relExpr = self.relExpr.applyTransitivity(nextRelExpr).checked({self.relExpr, nextRelExpr})
        else:#Updating an equals with an inequality!
            self.relExpr = nextRelExpr.applyTransitivity(self.relExpr).checked({self.relExpr,nextRelExpr})#.deriveReversed()
        return self.relExpr

    
    def proven(self, assumptions=frozenset()):
        '''
        Forwards this proven "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.ineqExpr.proven(assumptions)
        return self

    def qed(self, filename):
        '''
        Forwards this qed "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.ineqExpr.qed(filename)
        return self.eqExpr
