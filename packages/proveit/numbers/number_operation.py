from collections import deque, Counter
from proveit import (Expression, Judgment, Operation, ExprTuple, ExprRange,
                     generate_inner_expressions, USE_DEFAULTS,
                     prover, relation_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit.logic import Equals
from proveit.relation import TransRelUpdater
from proveit.abstract_algebra.generic_methods import (
        deduce_equality_via_commutation)
from .number_sets import (
    Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero,
    Interval, RealInterval)

class NumberOperation(Operation):
    '''
    Base class for number operation (i.e. arithmetic operations).
    '''
    
    def __init__(self, operator, operand_or_operands, *, styles=None):
        Operation.__init__(self, operator, operand_or_operands, styles=styles)

    def _deduce_equality(self, equality):
        '''
        Prove that this number operation is equal to an expression that 
        has the same canonical form.
        '''
        from proveit.numbers import Add, Mult, Div, Exp, Neg
        lhs, rhs = equality.lhs, equality.rhs
        assert lhs == self
        assert lhs.canonical_form() == rhs.canonical_form()

        # If the rhs is the same type as the lhs and the
        # canonical forms of the operands are the same, we can
        # use direct substitution and/or a permutation for operations
        # that commute (Add and Mult).
        if isinstance(rhs, type(lhs)):
            canonical_lhs_operands = [operand.canonical_form() for operand 
                                      in lhs.operands]
            canonical_rhs_operands = [operand.canonical_form() for operand 
                                      in rhs.operands]
            if canonical_lhs_operands == canonical_rhs_operands:
                # Just use direct substitution.
                return equality.conclude_via_direct_substitution()
            elif (isinstance(self, Add) or isinstance(self, Mult)) and (
                    Counter(canonical_lhs_operands) == 
                    Counter(canonical_rhs_operands)):
                # We just need direct substitution and permutation.
                return deduce_equality_via_commutation(equality, one_side=self)
        
        # Since the canonical forms are the same, we should be
        # able to equate their simplifications.
        # But make sure we use the proper simplification directives
        # (mostly the default ones).
        with Div.temporary_simplification_directives(use_defaults=True) as div_simps, \
             Exp.temporary_simplification_directives(use_defaults=True) as exp_simps:
            with Add.temporary_simplification_directives(use_defaults=True), \
                 Neg.temporary_simplification_directives(use_defaults=True), \
                 Mult.temporary_simplification_directives(use_defaults=True):
                # Reduce division to multiplication, consistent
                # with the canonical form.
                div_simps.reduce_to_multiplication = True
                # Distribute exponents consistent with the 
                # canonical form.
                exp_simps.distribute_exponent = True
                lhs_simplification = lhs.simplification()
                rhs_simplification = rhs.simplification()
        eq_simps = Equals(lhs_simplification.rhs, 
                          rhs_simplification.rhs).prove()
        return Equals.apply_transitivities([lhs_simplification,
                                            eq_simps,
                                            rhs_simplification])

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
            #print('inner_expr_bound', inner_expr_bound)
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
    Prove that 'expr' is an Expression that represents a number
    in a standard number set that is as restrictive as we can
    readily know.
    '''
    from proveit.logic import And, InSet, Equals, NotEquals
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
                                           styles=eq_expr.get_styles()))
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
        from proveit import defaults
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

# Map pairs of standard number sets to the minimal standard
# number set that contains them both. This dictionary is then
# used for the merge_two_sets() and merge_list_of_sets() fxns below.
merging_dict = {
    (NaturalPos, IntegerNeg): IntegerNonZero,
    (NaturalPos, Natural): Natural,
    (NaturalPos, IntegerNonPos): Integer,
    (NaturalPos, IntegerNonZero): IntegerNonZero,
    (NaturalPos, Integer): Integer,
    (NaturalPos, RationalPos): RationalPos,
    (NaturalPos, RationalNeg): RationalNonZero,
    (NaturalPos, RationalNonNeg): RationalNonNeg,
    (NaturalPos, RationalNonPos): Rational,
    (NaturalPos, RationalNonZero): RationalNonZero,
    (NaturalPos, Rational): Rational,
    (NaturalPos, RealPos): RealPos,
    (NaturalPos, RealNeg): RealNonZero,
    (NaturalPos, RealNonNeg): RealNonNeg,
    (NaturalPos, RealNonPos): Real,
    (NaturalPos, RealNonZero): RealNonZero,
    (NaturalPos, Real): Real,
    (NaturalPos, ComplexNonZero): ComplexNonZero,
    (NaturalPos, Complex): Complex,
    (IntegerNeg, Natural): Integer,
    (IntegerNeg, IntegerNonPos): IntegerNonPos,
    (IntegerNeg, IntegerNonZero): IntegerNonZero,
    (IntegerNeg, Integer): Integer,
    (IntegerNeg, RationalPos): RationalNonZero,
    (IntegerNeg, RationalNeg): RationalNeg,
    (IntegerNeg, RationalNonNeg): Rational,
    (IntegerNeg, RationalNonPos): RationalNonPos,
    (IntegerNeg, RationalNonZero): RationalNonZero,
    (IntegerNeg, Rational): Rational,
    (IntegerNeg, RealPos): Real,
    (IntegerNeg, RealNeg): RealNeg,
    (IntegerNeg, RealNonNeg): Real,
    (IntegerNeg, RealNonPos): Real,
    (IntegerNeg, RealNonZero): Real,
    (IntegerNeg, Real): Real,
    (IntegerNeg, ComplexNonZero): ComplexNonZero,
    (IntegerNeg, Complex): Complex,
    (Natural, IntegerNonPos): Integer,
    (Natural, IntegerNonZero): Integer,
    (Natural, Integer): Integer,
    (Natural, RationalPos): RationalNonNeg,
    (Natural, RationalNeg): Rational,
    (Natural, RationalNonNeg): RationalNonNeg,
    (Natural, RationalNonPos): Rational,
    (Natural, RationalNonZero): Rational,
    (Natural, Rational): Rational,
    (Natural, RealPos): RealNonNeg,
    (Natural, RealNeg): Real,
    (Natural, RealNonNeg): RealNonNeg,
    (Natural, RealNonPos): Real,
    (Natural, RealNonZero): Real,
    (Natural, Real): Real,
    (Natural, ComplexNonZero): Complex,
    (Natural, Complex): Complex,
    (IntegerNonPos, IntegerNonZero): Integer,
    (IntegerNonPos, Integer): Integer,
    (IntegerNonPos, RationalPos): Rational,
    (IntegerNonPos, RationalNeg): RationalNonPos,
    (IntegerNonPos, RationalNonNeg): Rational,
    (IntegerNonPos, RationalNonPos): RationalNonPos,
    (IntegerNonPos, RationalNonZero): Rational,
    (IntegerNonPos, Rational): Rational,
    (IntegerNonPos, RealPos): Real,
    (IntegerNonPos, RealNeg): RealNonPos,
    (IntegerNonPos, RealNonNeg): Real,
    (IntegerNonPos, RealNonPos): RealNonPos,
    (IntegerNonPos, RealNonZero): Real,
    (IntegerNonPos, Real): Real,
    (IntegerNonPos, ComplexNonZero): ComplexNonZero,
    (IntegerNonPos, Complex): Complex,
    (IntegerNonZero, Integer): Integer,
    (IntegerNonZero, RationalPos): RationalNonZero,
    (IntegerNonZero, RationalNeg): RationalNonZero,
    (IntegerNonZero, RationalNonNeg): Rational,
    (IntegerNonZero, RationalNonPos): Rational,
    (IntegerNonZero, RationalNonZero): RationalNonZero,
    (IntegerNonZero, Rational): Rational,
    (IntegerNonZero, RealPos): RealNonZero,
    (IntegerNonZero, RealNeg): RealNonZero,
    (IntegerNonZero, RealNonNeg): Real,
    (IntegerNonZero, RealNonPos): Real,
    (IntegerNonZero, RealNonZero): RealNonZero,
    (IntegerNonZero, Real): Real,
    (IntegerNonZero, ComplexNonZero): ComplexNonZero,
    (IntegerNonZero, Complex): Complex,
    (Integer, RationalPos): Rational,
    (Integer, RationalNeg): Rational,
    (Integer, RationalNonNeg): Rational,
    (Integer, RationalNonPos): Rational,
    (Integer, RationalNonZero): Rational,
    (Integer, Rational): Rational,
    (Integer, RealPos): Real,
    (Integer, RealNeg): Real,
    (Integer, RealNonNeg): Real,
    (Integer, RealNonPos): Real,
    (Integer, RealNonZero): Real,
    (Integer, Real): Real,
    (Integer, ComplexNonZero): Complex,
    (Integer, Complex): Complex,
    (RationalPos, RationalNeg): RationalNonZero,
    (RationalPos, RationalNonNeg): RationalNonNeg,
    (RationalPos, RationalNonPos): Rational,
    (RationalPos, RationalNonZero): RationalNonZero,
    (RationalPos, Rational): Rational,
    (RationalPos, RealPos): RealPos,
    (RationalPos, RealNeg): RealNonZero,
    (RationalPos, RealNonNeg): RealNonNeg,
    (RationalPos, RealNonPos): Real,
    (RationalPos, RealNonZero): RealNonZero,
    (RationalPos, Real): Real,
    (RationalPos, ComplexNonZero): ComplexNonZero,
    (RationalPos, Complex): Complex,
    (RationalNeg, RationalNonNeg): Rational,
    (RationalNeg, RationalNonPos): RationalNonPos,
    (RationalNeg, RationalNonZero): RationalNonZero,
    (RationalNeg, Rational): Rational,
    (RationalNeg, RealPos): RealNonZero,
    (RationalNeg, RealNeg): RealNeg,
    (RationalNeg, RealNonNeg): Real,
    (RationalNeg, RealNonPos): RealNonPos,
    (RationalNeg, RealNonZero): RealNonZero,
    (RationalNeg, Real): Real,
    (RationalNeg, ComplexNonZero): ComplexNonZero,
    (RationalNeg, Complex): Complex,
    (RationalNonNeg, RationalNonPos): Rational,
    (RationalNonNeg, RationalNonZero): Rational,
    (RationalNonNeg, Rational): Rational,
    (RationalNonNeg, RealPos): RealNonNeg,
    (RationalNonNeg, RealNeg): Real,
    (RationalNonNeg, RealNonNeg): RealNonNeg,
    (RationalNonNeg, RealNonPos): Real,
    (RationalNonNeg, RealNonZero): Real,
    (RationalNonNeg, Real): Real,
    (RationalNonNeg, ComplexNonZero): Complex,
    (RationalNonNeg, Complex): Complex,
    (RationalNonPos, RationalNonZero): Rational,
    (RationalNonPos, Rational): Rational,
    (RationalNonPos, RealPos): Real,
    (RationalNonPos, RealNeg): RealNonPos,
    (RationalNonPos, RealNonNeg): Real,
    (RationalNonPos, RealNonPos): RealNonPos,
    (RationalNonPos, RealNonZero): Real,
    (RationalNonPos, Real): Real,
    (RationalNonPos, ComplexNonZero): ComplexNonZero,
    (RationalNonPos, Complex): Complex,
    (RationalNonZero, Rational): Rational,
    (RationalNonZero, RealPos): RealNonZero,
    (RationalNonZero, RealNeg): RealNonZero,
    (RationalNonZero, RealNonNeg): Real,
    (RationalNonZero, RealNonPos): Real,
    (RationalNonZero, RealNonZero): RealNonZero,
    (RationalNonZero, Real): Real,
    (RationalNonZero, ComplexNonZero): ComplexNonZero,
    (RationalNonZero, Complex): Complex,
    (Rational, RealPos): Real,
    (Rational, RealNeg): Real,
    (Rational, RealNonNeg): Real,
    (Rational, RealNonPos): Real,
    (Rational, RealNonZero): Real,
    (Rational, Real): Real,
    (Rational, ComplexNonZero): Complex,
    (Rational, Complex): Complex,
    (RealPos, RealNeg): RealNonZero,
    (RealPos, RealNonNeg): RealNonNeg,
    (RealPos, RealNonPos): Real,
    (RealPos, RealNonZero): RealNonZero,
    (RealPos, Real): Real,
    (RealPos, ComplexNonZero): ComplexNonZero,
    (RealPos, Complex): Complex,
    (RealNeg, RealNonNeg): Real,
    (RealNeg, RealNonPos): RealNonPos,
    (RealNeg, RealNonZero): RealNonZero,
    (RealNeg, Real): Real,
    (RealNeg, ComplexNonZero): ComplexNonZero,
    (RealNeg, Complex): Complex,
    (RealNonNeg, RealNonPos): Real,
    (RealNonNeg, RealNonZero): Real,
    (RealNonNeg, Real): Real,
    (RealNonNeg, ComplexNonZero): Complex,
    (RealNonNeg, Complex): Complex,
    (RealNonPos, RealNonZero): Real,
    (RealNonPos, Real): Real,
    (RealNonPos, ComplexNonZero): ComplexNonZero,
    (RealNonPos, Complex): Complex,
    (RealNonZero, Real): Real,
    (RealNonZero, ComplexNonZero): ComplexNonZero,
    (RealNonZero, Complex): Complex,
    (Real, ComplexNonZero): Complex,
    (Real, Complex): Complex,
    (ComplexNonZero, Complex): Complex}

def merge_two_sets(set_01, set_02):
    '''
    A utility function to return the minimal standard number set
    that contains both set_01 and set_02. Notice that this does
    not prove the inclusion; it just provides a set that should
    be proveable under the right conditions. This utility function
    is utilized in the merge_list_of_sets() functions further below.
    '''
    if (set_01, set_02) in merging_dict:
        return merging_dict[(set_01, set_02)]
    elif (set_02, set_01) in merging_dict:
        return merging_dict[(set_02, set_01)]
    # default is to return Real if Real actually works
    elif (Real.includes(set_01) and Real.includes(set_02)):
        return Real
    else:
        raise ValueError(
                "In calling merge_two_sets on sets {0} and {1}, "
                "no standard number set was found that contained "
                "both sets.".format(set_01, set_02))

def merge_list_of_sets(list_of_sets):
    '''
    Utility function to produce a minimal standard number set that
    contains all the number sets in list_of_sets, if possible.
    Notice that the function does not prove the result, instead just
    providing a superset that should be proveable under the right
    conditions.
    '''
    while len(list_of_sets) > 1:
        if list_of_sets[0] == list_of_sets[1]:
            list_of_sets = ([list_of_sets[0]]+list_of_sets[2:])
        else:
            list_of_sets = (
                    [merge_two_sets(list_of_sets[0],
                                    list_of_sets[1])]+list_of_sets[2:])
    return list_of_sets[0]

