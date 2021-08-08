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
        updates.
        '''
        from proveit.logic import Equals
        self.expr = expr
        self.relation = Equals(expr, expr).conclude_via_reflexivity()
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
        if assumptions is None:
            assumptions = self.assumptions
        relation_reversed = relation.is_reversed()
        self.relation = self.relation.apply_transitivity(
                relation, assumptions=assumptions, preserve_all=True)
        if relation.lhs == self.expr:
            self.expr = relation.rhs
        elif relation.rhs == self.expr:
            self.expr = relation.lhs
        else:
            raise ValueError("Relation %s should match expression %s "
                             "on one of its sides." % (relation, self.expr))
        if relation_reversed != self.relation.is_reversed():
            # Reverse to match the "direction" of the provided relation.
            self.relation = self.relation.with_direction_reversed()
        return self.expr
