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
        from proveit.logic import Equals
        if assumptions is None:
            assumptions = self.assumptions
        if isinstance(relation, Judgment):
            relation = relation.expr
        if isinstance(relation, Equals) and (
                relation.lhs == relation.rhs == self.expr):
            # We can disregard this trivial reflexive relation: x=x.
            return self.expr
        self.relations.append(relation)
        if relation.lhs == self.expr:
            self.expr = relation.rhs
        elif relation.rhs == self.expr:
            self.expr = relation.lhs
        else:
            raise ValueError("Relation %s should match expression %s "
                             "on one of its sides." % (relation, self.expr))
        return self.expr
    
    @property
    def relation(self):
        from proveit.logic import Equals
        from .transitivity import TransitiveRelation
        relations = self.relations
        if len(relations) == 0:
            # Trivial, reflexive x=x.
            return Equals(self.expr, self.expr).conclude_via_reflexivity()
        return TransitiveRelation.apply_transitivities(relations)
