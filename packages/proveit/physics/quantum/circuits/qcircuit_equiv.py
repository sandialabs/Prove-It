from proveit import (Literal, Lambda, TransitiveRelation, Judgment,
                     prover, USE_DEFAULTS)
from proveit import j, k, l, m, A, B, C, D
from .qcircuit import Qcircuit

class QcircuitEquiv(TransitiveRelation):
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
        TransitiveRelation.__init__(self, QcircuitEquiv._operator_, a, b,
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
    
    @prover
    def _sub_one_side_into(self, circuit_or_lambda_map, *,
                           which_side, **defaults_config):
        '''
        Helper method for sub_[left/right]_side_into.
        '''
        lhs, rhs = self.lhs, self.rhs
        if which_side=='left':
            old, new = rhs, lhs
        elif which_side=='right':
            old, new = lhs, rhs
        else:
            raise ValueError("'which_side' must either be 'left' or 'right'")
        
        if isinstance(circuit_or_lambda_map, Judgment):
            circuit_or_lambda_map = circuit_or_lambda_map.expr
        
        if isinstance(circuit_or_lambda_map, Qcircuit):
            from . import circuit_equiv_temporal_sub
            # When simply given a Qcircuit, assume 'old' part is
            # embedded in a consecutive subset of this circuit and
            # we just need to swap it out.
            circuit = circuit_or_lambda_map
            circuit_columns = circuit.vert_expr_array
            _start = circuit_columns.find_sub_tuple(old.vert_expr_array)
            if _start==-1:
                raise ValueError(
                        "Quantum circuit not found among consecutive "
                        "columns of other circuit: %s not in %s"
                        %(old, circuit_columns))
            _end = _start+old.vert_expr_array.num_entries()
            _A = circuit_columns[:_start]
            _B = circuit_columns[_start:_end]
            _C = circuit_columns[_end:]
            assert _B.entries == old.vert_expr_array.entries
            _D = new.vert_expr_array
            _j = _A.num_elements()
            _k = _B.num_elements()
            _l = _C.num_elements()
            _m = _D.num_elements()
            impl = circuit_equiv_temporal_sub.instantiate(
                    {j:_j, k:_k, l:_l, m:_m, A:_A, B:_B, C:_C, D:_D})
            equiv = impl.derive_consequent()
            return equiv.derive_right_via_equiv()

    def sub_left_side_into(self, circuit_or_lambda_map, 
                           assumptions=USE_DEFAULTS):
        '''
        Derive a new quantum circuit from a proven one by
        substituting the left side of the equivalence in place
        of an occurrence of the right side.
        When given an actual Qcircuit for 'circuit_or_lambda_map', just
        find the sub-circuit to replace as a consecutive subset of
        columns.  Specifying a lambda map, a specific portion may
        be indicated over any subset of rows.
        '''
        return self._sub_one_side_into(circuit_or_lambda_map,
                                       which_side = 'left')

    def sub_right_side_into(self, circuit_or_lambda_map, 
                           assumptions=USE_DEFAULTS):
        '''
        Derive a new quantum circuit from a proven one by
        substituting the right side of the equivalence in place
        of an occurrence of the left side.
        When given an actual Qcircuit for 'circuit_or_lambda_map', just
        find the sub-circuit to replace as a consecutive subset of
        columns.  Specifying a lambda map, a specific portion may
        be indicated over any subset of rows.
        '''
        return self._sub_one_side_into(circuit_or_lambda_map,
                                       which_side = 'right')        

    def derive_right_via_equiv(self):
        '''
        Derive from this equivalence that its right side is true
        provided that its left side is true.
        '''
        from . import rhs_via_equiv
        return rhs_via_equiv.instantiate({A:self.lhs, B:self.rhs})

    def derive_left_via_equiv(self):
        '''
        Derive from this equivalence that its right side is true
        provided that its left side is true.
        '''
        from . import lhs_via_equiv
        return lhs_via_equiv.instantiate({A:self.lhs, B:self.rhs})
