from proveit import Literal, Lambda, TransitiveRelation, USE_DEFAULTS

class CircuitEquiv(TransitiveRelation):
    '''
    Class to capture the equivalence of 2 circuits A and B.
    CircuitEquiv(A, B) is a claim that the inputs and outputs of A are
    equivalent to the inputs and outputs of B, regardless of what is in between.
    The CircuitEquiv relation uses the congruence
    symbol to distinguish the CircuitEquiv claim from the stronger claim
    that A = B.
    '''
    # operator for the CircuitEquiv relation
    _operator_ = Literal(string_format='equiv', latex_format=r'\cong',
                         theory=__file__)
    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, a, b, *, styles=None):
        TransitiveRelation.__init__(self, CircuitEquiv._operator_, a, b,
                                    styles=styles)
        self.a = a
        self.b = b

    @staticmethod
    def _lambda_expr(
            lambda_map,
            expr_being_replaced,
            assumptions=USE_DEFAULTS):
        from proveit import ExprRange, InnerExpr
        if isinstance(lambda_map, InnerExpr):
            lambda_map = lambda_map.repl_lambda()
        if not isinstance(lambda_map, Lambda):
            # as a default, do a global replacement
            lambda_map = Lambda.global_repl(lambda_map, expr_being_replaced)
        if not lambda_map.parameters.is_single():
            raise ValueError("When substituting, expecting a single "
                             "'lambda_map' parameter entry which may "
                             "be a single parameter or a range; got "
                             "%s as 'lambda_map'" % lambda_map)
        if isinstance(lambda_map.parameters[0], ExprRange):
            from proveit.numbers import one
            if lambda_map.parameters[0].start_index != one:
                raise ValueError("When substituting a range, expecting "
                                 "the 'lambda_map' parameter range to "
                                 "have a starting index of 1; got "
                                 "%s as 'lambda_map'" % lambda_map)
        return lambda_map

    """
    def substitution(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given f(x), derive f(x) equiv f(y).
        f(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange
        from . import substitution
        from proveit import f, x, y

        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.lhs, assumptions)
        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use operands_substitution for ExprTuple
            # substitution.
            from proveit.core_expr_types.operations import \
                operands_substitution
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return operands_substitution.instantiate(
                {n: n_sub, f: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)
        '''
        # Regular single-operand substitution:
        return substitution.instantiate({f: lambda_map, x: self.lhs, y: self.rhs},
                                        assumptions=assumptions)
    """

    def sub_left_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given P(y), derive P(x) assuming P(y).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        # from proveit import ExprRange
        from . import sub_left_side_into
        # from . import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        from proveit import P, x, y
        # from proveit.logic import TRUE, FALSE
        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.rhs)

        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_left_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_left_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_left_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)

        try:
            # try some alternative proofs that may be shorter, if they
            # are usable
            if self.rhs == TRUE:
                # substitute_truth may provide a shorter proof option
                substitute_truth.instantiate({x: self.lhs, P: lambda_map},
                                           assumptions=assumptions)
            elif self.lhs == TRUE:
                # substitute_in_true may provide a shorter proof option
                substitute_in_true.instantiate({x: self.rhs, P: lambda_map},
                                            assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_falsehood may provide a shorter proof option
                substitute_falsehood.instantiate({x: self.lhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_in_false may provide a shorter proof option
                substitute_in_false.instantiate({x: self.rhs, P: lambda_map},
                                             assumptions=assumptions)
        except:
            pass
        '''
        return sub_left_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)

    def sub_right_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given P(x), derive P(y) assuming P(x).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange
        from . import sub_right_side_into
        # from . import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        # from proveit.logic import TRUE, FALSE
        from proveit import P, x, y
        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.lhs)

        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_right_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_right_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_right_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)

        try:
            # try some alternative proofs that may be shorter, if they are usable
            if self.lhs == TRUE:
                # substitute_truth may provide a shorter proof options
                substitute_truth.instantiate({x: self.rhs, P: lambda_map},
                                           assumptions=assumptions)
            elif self.rhs == TRUE:
                # substitute_in_true may provide a shorter proof options
                substitute_in_true.instantiate({x: self.lhs, P: lambda_map},
                                            assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_falsehood may provide a shorter proof options
                substitute_falsehood.instantiate({x: self.rhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_in_false may provide a shorter proof options
                substitute_in_false.instantiate({x: self.lhs, P: lambda_map},
                                             assumptions=assumptions)
        except:
            pass
        '''
        return sub_right_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)
