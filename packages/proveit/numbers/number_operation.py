from collections import deque
from proveit import (Expression, Judgment, Operation, ExprTuple, ExprRange,
                     generate_inner_expressions, USE_DEFAULTS,
                     prover, relation_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit.relation import TransRelUpdater
from .number_sets import (
    Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero)

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
            raise ValueError("Expecting one or more 'inner_expr_bounds'")
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
                # Don't simplify or make replacements if there
                # is more to go:
                preserve_all = (len(inner_expr_bounds) > 0)
                container_relation.update(expr.bound_via_operand_bound(
                        inner_expr_bound, preserve_all=preserve_all))
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
    '''
    Prove that 'expr' is an Expression that respresents a number
    in the given 'number_set'.
    '''
    from proveit.logic import InSet
    membership = InSet(expr, number_set)
    if membership.proven():
        # Already proven. We're done.
        return membership.prove()
    if hasattr(expr, 'deduce_in_number_set'):
        # Use 'deduce_in_number_set' method.
        return expr.deduce_in_number_set(number_set)
    # Try prove().
    return membership.prove()

def quick_simplified_index(expr):
    '''
    Return a simplified version of this expression with a 
    quick-n-dirty approach suitable for additively shifted and/or
    negated integer indices and nested versions thereof.
    In particular, negations are distributed nested additionas are 
    ungrouped, literal integers are extracted, added, and placed at the
    end, and cancelations are made on ndividual terms as well as 
    expression ranges or portions of expression ranges.  We freely 
    assume terms represent numbers and expression ranges are 
    well-formed.
    Used for ExprRange formatting and for hints along the way when
    provably expanding ExprRanges through an instantiation (this
    provides hints, but there will be proven requirements to ensure it
    is right).
    '''
    from proveit.numbers import Add, Neg
    if isinstance(expr, Neg):
        return Add(expr).quick_simplified()
    elif isinstance(expr, Add):
        return expr.quick_simplified()
    return expr

# Sorted standard number sets from most restrictive to least
# restrictive.
sorted_number_sets = (
    NaturalPos, IntegerNeg, Natural, IntegerNonPos, 
    IntegerNonZero, Integer,
    RationalPos, RationalNeg, RationalNonNeg, RationalNonPos,
    RationalNonZero, Rational,
    RealPos, RealNeg, RealNonNeg, RealNonPos,
    RealNonZero, Real,
    ComplexNonZero, Complex)

standard_number_sets = set(sorted_number_sets)

# Map number sets to the positive number set it contains.
pos_number_set = {
    NaturalPos: NaturalPos,
    Natural: NaturalPos,
    IntegerNonZero: NaturalPos,
    Integer: NaturalPos,
    RationalPos: RationalPos,
    RationalNonNeg: RationalPos,
    RationalNonZero: RationalPos,
    Rational: RationalPos,
    RealPos: RealPos,
    RealNonNeg: RealPos,
    RealNonZero: RealPos,
    Real: RealPos,
    Complex: RealPos,
    ComplexNonZero: RealPos}

# Map number sets to the negative number set it contains.
neg_number_set = {
    IntegerNeg: IntegerNeg,
    IntegerNonPos: IntegerNeg,
    IntegerNonZero: IntegerNeg,
    Integer: IntegerNeg,
    RationalNeg: RationalNeg,
    RationalNonPos: RationalNeg,
    RationalNonZero: RationalNeg,
    Rational: RationalNeg,
    RealNeg: RealNeg,
    RealNonPos: RealNeg,
    RealNonZero: RealNeg,
    Real: RealNeg,
    Complex: RealNeg,
    ComplexNonZero: RealNeg}

# Map number sets to the non-negative number set it contains.
nonneg_number_set = {
    Natural: Natural,
    IntegerNonZero: Natural,
    Integer: Natural,
    RationalNonNeg: RationalNonNeg,
    RationalNonZero: RationalNonNeg,
    Rational: RationalNonNeg,
    RealNonNeg: RealNonNeg,
    RealNonZero: RealNonNeg,
    Real: RealNonNeg,
    Complex: RealNonNeg,
    ComplexNonZero: RealNonNeg}

# Map number sets to the non-positive number set it contains.
nonpos_number_set = {
    IntegerNonPos: IntegerNonPos,
    IntegerNonZero: IntegerNonPos,
    Integer: IntegerNonPos,
    RationalNonPos: RationalNonPos,
    RationalNonZero: RationalNonPos,
    Rational: RationalNonPos,
    RealNonPos: RealNonPos,
    RealNonZero: RealNonPos,
    Real: RealNonPos,
    Complex: RealNonPos,
    ComplexNonZero: RealNonPos}

# Map number sets to the non-zero number set it contains.
nonzero_number_set = {
    IntegerNonPos: IntegerNeg,
    Natural: NaturalPos,
    IntegerNonZero: IntegerNonZero,
    Integer: IntegerNonZero,
    RationalNonPos: RationalNeg,
    RationalNonNeg: RationalPos,
    RationalNonZero: RationalNonZero,
    Rational: RationalNonZero,
    RealNonPos: RealNeg,
    RealNonNeg: RealPos,
    RealNonZero: RealNonZero,
    Real: RealNonZero,
    Complex: ComplexNonZero,
    ComplexNonZero: ComplexNonZero}

@relation_prover
def deduce_number_set(expr, **defaults_config):
    '''
    Prove that 'expr' is an Expression that respresents a number
    in a standard number set that is as restrictive as we can
    readily know.
    '''
    from proveit.logic import InSet, Equals, NotEquals
    from proveit.numbers import Less, LessEq, zero

    # Find the first (most restrictive) number set that
    # contains 'expr' or something equal to it.
    for number_set in sorted_number_sets:
        membership = None
        for eq_expr in Equals.yield_known_equal_expressions(expr):
            if isinstance(eq_expr, ExprRange):
                membership = And(ExprRange(eq_expr.parameter, 
                                           InSet(eq_expr.body, number_set),
                                           eq_expr.true_start_index,
                                           eq_expr.true_end_index,
                                           styles=eq_expr.styles))
            else:
                membership = InSet(eq_expr, number_set)
            if membership.proven():
                break # found a known number set membership
            else:
                membership = None
        if membership is not None:
            membership = InSet(expr, number_set).prove()
            break

    if hasattr(expr, 'deduce_number_set'):
        # Use 'deduce_number_set' method.
        try:
            deduced_membership = expr.deduce_number_set()
        except (UnsatisfiedPrerequisites, ProofFailure):
            deduced_membership = None
        if deduced_membership is not None:
            assert isinstance(deduced_membership, Judgment)
            if not isinstance(deduced_membership.expr, InSet):
                raise TypeError("'deduce_number_set' expected to prove an "
                                "InSet type expression")
            if deduced_membership.expr.element != expr:
                raise TypeError("'deduce_number_set' was expected to prove "
                                "that %s is in some number set"%expr)
            # See if this deduced number set is more restrictive than
            # what we had surmised already.
            deduced_number_set = deduced_membership.domain
            if membership is None:
                membership = deduced_membership
                number_set = deduced_number_set
            elif (deduced_number_set != number_set and number_set.includes(
                    deduced_number_set)):
                number_set = deduced_number_set
                membership = deduced_membership

    if membership is None:
        raise UnsatisfiedPrerequisites(
            "Unable to prove any number membership for %s"%expr)

    # Already proven to be in some number set,
    # Let's see if we can restrict it further.
    if Less(zero, expr).proven(): # positive
        number_set = pos_number_set.get(number_set, None)
    elif Less(expr, zero).proven(): # negative
        number_set = neg_number_set.get(number_set, None)
    elif LessEq(zero, expr).proven(): # non-negative
        number_set = nonneg_number_set.get(number_set, None)
    elif LessEq(expr, zero).proven(): # non-positive
        number_set = nonpos_number_set.get(number_set, None)
    elif NotEquals(expr, zero).proven():
        number_set = nonzero_number_set.get(number_set, None)
    if number_set is None:
        # Just use what we have already proven.
        return membership.prove()
    return InSet(expr, number_set).prove()

def standard_number_set(given_set, **defaults_config):
    '''
    For the number set given_set (which might, for example, be a
    continuous interval, an integer interval, etc.), return the most
    restrictive number set (such as Real, RealPos, Integer, etc.)
    that is already known to contain the given_set, or return the
    original given_set if no such standard set inclusion is already
    known.
    '''
    for std_number_set in sorted_number_sets:
        # return the first std set that includes our given_set
        if std_number_set.includes(given_set):
            return std_number_set

    # return the original given_set if the
    # for loop above didn't find anything
    return given_set
