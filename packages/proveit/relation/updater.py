from proveit import Judgment, USE_DEFAULTS


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
        self.expr = expr
        self.relations = []
        self.assumptions = assumptions

    def update(self, relation):
        '''
        Update the internal relation by applying transitivity
        with the given relation.  Return the new expression
        that is introduced.  For example, if the internal
        expression is 'b' and the internal relation is
        'a < b' and 'b < c' is provided, deduce
        'a < c' as the new internal relation and
        return 'c' as the new internal expression.
        '''
        from proveit.logic import Equals
        if isinstance(relation, Judgment):
            relation = relation.expr
        if isinstance(relation, Equals) and (
                relation.lhs == relation.rhs == self.expr):
            # We can disregard this trivial reflexive relation: x=x.
            return self.expr
        if relation.rhs == self.expr:
            if hasattr(relation, 'derive_reversed'):
                relation = relation.derive_reversed()
            else:
                relation = relation.with_direction_reversed()
        elif relation.lhs != self.expr:
            raise ValueError("Relation %s should match expression %s "
                             "on one of its sides." % (relation, self.expr))
        self.expr = relation.rhs
        self.relations.append(relation)
        return self.expr
    
    def inner_expr(self):
        '''
        Return the InnerExpr of the current expression.
        '''
        return self.expr.inner_expr()
    
    @property
    def relation(self):
        from proveit.logic import Equals
        from .transitivity import TransitiveRelation
        relations = self.relations
        if len(relations) == 0:
            # Trivial, reflexive x=x.
            return Equals(self.expr, self.expr).conclude_via_reflexivity()
        return TransitiveRelation.apply_transitivities(
                relations, assumptions=self.assumptions)
