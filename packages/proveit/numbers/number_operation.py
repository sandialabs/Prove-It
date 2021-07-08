from proveit import (Expression, Judgment, Operation, ExprTuple,
                     generate_inner_expressions, USE_DEFAULTS,
                     prover, relation_prover)
from proveit.relation import TransRelUpdater
from collections import deque

class NumberOperation(Operation):
    '''
    Base class for number operation (i.e. arithmetic operations).
    '''
    
    def __init__(self, operator, operand_or_operands, *, styles=None):
        Operation.__init__(self, operator, operand_or_operands, styles=styles)

    @relation_prover
    def deduce_bound(self, inner_expr_bound_or_bounds, 
                     inner_exprs_to_bound = None,
                     **defaults_config):
        '''
        Return a bound of this arithmetic expression based upon
        the bounds of any number of inner expressions.  The inner 
        expression should appear on the left side of the corresponding
        bound which should be a number ordering relation (< or <=).
        The returned, proven bound will have this expression on the 
        left-hand side.  The bounds of the inner expressions will be
        processed in the order they are provided.
        
        If inner_exprs_to_bound is provided, restrict the bounding
        to these particular InnerExpr objects.  Otherwise, all inner
        expressions are fair game.
        '''
        if isinstance(inner_expr_bound_or_bounds, Judgment):
            inner_expr_bound_or_bounds = inner_expr_bound_or_bounds.expr
        if isinstance(inner_expr_bound_or_bounds, ExprTuple):
            inner_expr_bounds = inner_expr_bound_or_bounds.entries
        elif isinstance(inner_expr_bound_or_bounds, Expression):
            inner_expr_bounds = [inner_expr_bound_or_bounds]
        else:
            inner_expr_bounds = inner_expr_bound_or_bounds
        inner_expr_bounds = deque(inner_expr_bounds)
        inner_relations = dict()
        if len(inner_expr_bounds) == 0:
            raise ValueError("Expecting on or more 'inner_expr_bounds'")
        while len(inner_expr_bounds) > 0:
            inner_expr_bound = inner_expr_bounds.popleft()
            if isinstance(inner_expr_bound, TransRelUpdater):
                # May be one of the internally generated
                # TransRelUpdater for percolating bounds up through
                # the expression hierarchy to the root.
                inner_expr_bound = inner_expr_bound.relation
            elif isinstance(inner_expr_bound, Judgment):
                inner_expr_bound = inner_expr_bound.expr
            inner = inner_expr_bound.lhs
            if inner == self:
                raise ValueError(
                        "Why supply a bound for the full expression when "
                        "calling 'deduce_bound'? There is nothing to deduce.")
            no_such_inner_expr = True
            no_such_number_op_inner_expr = True
            # Apply bound to each inner expression as applicable.
            if inner_exprs_to_bound is None:
                inner_exprs = generate_inner_expressions(self, inner) 
            else:
                inner_exprs = inner_exprs_to_bound                                
            for inner_expr in inner_exprs:
                no_such_inner_expr = False
                inner_expr_depth = len(inner_expr.expr_hierarchy)
                assert inner_expr_depth > 1, (
                        "We already checked that the inner expression was not "
                        "equal to the full expression. What's the deal?")
                # Create/update the relation for the container of this
                # inner expression.
                if inner_expr_depth >= 3:            
                    container = inner_expr.expr_hierarchy[-2]
                    if isinstance(container, ExprTuple):
                        # Skip an ExprTuple layer.
                        if inner_expr_depth >= 4:
                            container = inner_expr.expr_hierarchy[-3]
                        else:
                            container = self
                else:
                    container = self
                if not isinstance(container, NumberOperation):
                    # Skip over any 'container' that is not a
                    # NumberOperation.
                    continue
                no_such_number_op_inner_expr = False
                container_relation = inner_relations.setdefault(
                        container, TransRelUpdater(container))
                expr = container_relation.expr
                container_relation.update(expr.bound_via_operand_bound(
                        inner_expr_bound))
                # Append the relation for processing
                if container is self:
                    # No further processing needed when the container
                    continue # is self.
                if (len(inner_expr_bounds) == 0 or 
                        inner_expr_bounds[-1] != container_relation):
                    inner_expr_bounds.append(container_relation)
            if no_such_inner_expr:
                raise ValueError(
                        "The left side of %s does not appear within %s"
                        %(inner_expr_bound, self))
            if no_such_number_op_inner_expr:
                raise ValueError(
                        "The left side of %s is not contained within a "
                        "NumberOperation expression"
                        %(inner_expr_bound, self))
        assert self in inner_relations, (
                "If there are more than one inner bounds and they are "
                "valid, they should have percolated to the top")
        return inner_relations[self].relation

    @relation_prover
    def bound_via_operand_bound(self, operand_bound, **defaults_config):
        '''
        Return a bound of this arithmetic expression based upon
        the bound of one of its operands.  The operand should appear
        on the left side of the operand_bound which should be a
        number ordering relation (< or <=).  The returned, proven
        bound will have this expression on the left-hand side.
        
        Also see NumberOperation.deduce_bound.
        '''
        raise NotImplementedError(
                "'bound_via_operand_bound' not implemented for %s of type %s."
                %(self, self.__class__))

@relation_prover
def deduce_in_number_set(expr, number_set, **defaults_config):
    from proveit.logic import InSet
    if hasattr(expr, 'deduce_in_number_set'):
        return expr.deduce_in_number_set(number_set)
    return InSet(expr, number_set).prove()
