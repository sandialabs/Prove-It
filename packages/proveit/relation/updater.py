from proveit import USE_DEFAULTS

class TransRelUpdater:
    '''
    Transitive relation updater: A convenient class for
    updating a transitive relation (equality, less, subset,
    etc.) by adding relations that modify the relation
    via transitivity.
    '''
    def __init__(self, expr, assumptions=USE_DEFAULTS):
        '''
        Create a TransRelUpdater starting with the given
        expression and forming the trivial relation of
        expr=expr.  By providing 'assumptions', they
        can be used as default assumptions when applying
        updates. Modified 1/19/2020 by wdc to allow use
        with Set class and SetEquiv relation.
        '''
        from proveit.logic import Equals, Set, SetEquiv
        self.expr = expr
        print("init TransRelUpdater, expr = {}".format(expr))                   # for testing; delete later
        if isinstance(expr, Set):
            self.relation = SetEquiv(expr, expr).prove()
        else:
            self.relation = Equals(expr, expr).prove()
        self.assumptions = assumptions
    
    def update(self, relation, assumptions=None):
        '''
        Update the internal relation by applying transitivity
        with the given relation.  Return the new expression
        that is introduced.  For example, if the internal
        expression is 'b' and the internal relation is 
        'a < b' and 'b < c' is provided, deduce
        'a < c' as the new internal relation and 
        return 'c' as the new internal expression.
        '''
        if assumptions is None: assumptions=self.assumptions
        self.relation = self.relation.applyTransitivity(relation, assumptions)
        if relation.lhs == self.expr:
            self.expr = relation.rhs
        elif relation.rhs == self.expr:
            self.expr = relation.lhs
        return self.expr
