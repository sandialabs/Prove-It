from proveit import (Literal, Lambda, VertExprArray, TransitiveRelation, 
                     InnerExpr, TransitivityException,
                     as_expression, Judgment, prover, 
                     defaults, USE_DEFAULTS)
from proveit import j, k, l, m, A, B, C, D, Q
from proveit.relation import TransRelUpdater
from proveit.statistics import Prob
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

    def side_effects(self, judgment):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt derive_reversed.
        '''        
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        yield self.derive_reversed

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
            if lambda_map.parameters[0].true_start_index != one:
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
            assert lambda_map.parameters[0].true_start_index == one
            n_sub = lambda_map.parameters[0].true_end_index
            return operands_substitution.instantiate(
                {n: n_sub, f: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)
        '''
        # Regular single-operand substitution:
        return substitution.instantiate({f: lambda_map, x: self.lhs, y: self.rhs},
                                        assumptions=assumptions)
    """

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to prove that this QcircuitEquiv is true via automation.
        '''
        lhs_cols, rhs_cols = (self.lhs.vert_expr_array.entries, 
                              self.rhs.vert_expr_array.entries)
        if (len(lhs_cols) == len(rhs_cols) and
                all(lhs_col == rhs_col for lhs_col, rhs_col in zip(
                        lhs_cols[1:-1], rhs_cols[1:-1]))):
            # All inner columns are the same.  Try to
            # prove by consolidating inputs/outputs.
            return self.conclude_via_inout_consolidation()

    @prover
    def conclude_via_inout_consolidation(self, **defaults_config):
        '''
        Prove this circuit equivalence by consolidating the input
        (at the beginning) and/or output (at the end).
        '''
        lhs_cols, rhs_cols = (self.lhs.vert_expr_array.entries, 
                              self.rhs.vert_expr_array.entries)
        if len(lhs_cols) != len(rhs_cols):
            raise ValueError(
                    "Cannot perform 'conclude_via_inout_consolidation' "
                    "if the number of columns is different: %s ≠ %s."
                    %(len(lhs_cols), len(rhs_cols)))
        if not all(lhs_col == rhs_col for lhs_col, rhs_col in zip(
                lhs_cols[1:-1], rhs_cols[1:-1])):
            raise ValueError(
                    "Cannot perform 'conclude_via_inout_consolidation' "
                    "if the inner columns do not all match.")
        expr = self.lhs
        # Use this updater to go from the lhs to the rhs via
        # transitive equivalences.
        equiv = TransRelUpdater(expr)
        if lhs_cols[0] != rhs_cols[0]:
            # The first column does not match, so try to consolidate
            # inputs.
            lhs_consolidation = Qcircuit(
                    VertExprArray(lhs_cols[0])).input_consolidation()
            expr = equiv.update(lhs_consolidation.substitution(expr))
            rhs_consolidation = Qcircuit(
                    VertExprArray(rhs_cols[0])).input_consolidation()
            input_equiv = QcircuitEquiv(lhs_consolidation.rhs, 
                                        rhs_consolidation.rhs).prove()
            expr = equiv.update(input_equiv.substitution(expr))
            expr = equiv.update(rhs_consolidation.substitution(expr))
        if lhs_cols[-1] != rhs_cols[-1]:
            # The first column does not match, so try to consolidate
            # inputs.
            lhs_consolidation = Qcircuit(
                    VertExprArray(lhs_cols[-1])).output_consolidation()
            expr = equiv.update(lhs_consolidation.substitution(expr))
            rhs_consolidation = Qcircuit(
                    VertExprArray(rhs_cols[-1])).output_consolidation()
            output_equiv = QcircuitEquiv(lhs_consolidation.rhs, 
                                         rhs_consolidation.rhs).prove()
            expr = equiv.update(output_equiv.substitution(expr))
            expr = equiv.update(rhs_consolidation.substitution(expr))
        return equiv.relation

    @prover
    def apply_transitivity(self, other, **defaults_config):
        '''
        Apply a transitivity rule to derive from this x<y expression
        and something of the form y<z, y<=z, z>y, z>=y, or y=z to
        obtain x<z.
        '''
        from proveit.logic import Equals
        from . import equiv_transitivity
        other = as_expression(other)
        if isinstance(other, Equals):
            return TransitiveRelation.apply_transitivity(
                self, other)  # handles this special case
        elif self.rhs == other.lhs:
            return equiv_transitivity.instantiate(
                {A: self.lhs, B: self.rhs, C: other.rhs},
                preserve_all=True)
        elif self.rhs == other.rhs:
            return equiv_transitivity.instantiate(
                {A: self.lhs, B: self.rhs, C: other.lhs},
                preserve_all=True)
        elif self.lhs == other.lhs:
            return equiv_transitivity.instantiate(
                {A: self.rhs, B: self.lhs, C: other.rhs},
                preserve_all=True)
        elif self.lhs == other.rhs:
            return equiv_transitivity.instantiate(
                {A: self.rhs, B: self.lhs, C: other.lhs},
                preserve_all=True)
        else:
            raise TransitivityException(
                None,
                defaults.assumptions,
                'Transitivity cannot be applied unless there is something '
                'in common in the equalities: %s vs %s' %
                (str(self), str(other)))
    
    @prover
    def derive_reversed(self, **defaults_config):
        '''
        From A ≅ B, derive B ≅ A.
        '''
        from . import equiv_reflexivity
        return equiv_reflexivity.instantiate(
                {A:self.lhs, B:self.rhs})
    
    @prover # Note: this should NOT be an @equality_prover.
    def substitution(self, circuit_or_lambda_map, **defaults_config):
        '''
        From A ≅ B, and given a quantum circuit containing A, Q(A), 
        derive Q(A)≅Q(B).
        '''      
        old, new = self.lhs, self.rhs
        
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
            return equiv.without_wrapping()
        raise NotImplementedError()
        
    @prover
    def _sub_one_side_into(self, prob_relation_or_inner_expr, *,
                           which_side, **defaults_config):
        '''
        Helper method for sub_[left/right]_side_into.
        '''
        from . import lhs_prob_via_equiv, rhs_prob_via_equiv
        equiv = self
        if which_side=='left':
            thm = lhs_prob_via_equiv
            orig_circuit = equiv.rhs
        elif which_side=='right':
            thm = rhs_prob_via_equiv
            orig_circuit = equiv.lhs
        else:
            raise ValueError("'which_side' must either be 'left' or 'right'")
        if isinstance(prob_relation_or_inner_expr, InnerExpr):
            # This should be an inner expresion of a probability 
            # over a quantum circuit.
            inner_expr = prob_relation_or_inner_expr
            expr_hierarchy = inner_expr.expr_hierarchy
            for _k, _expr in enumerate(reversed(expr_hierarchy)):
                circuit_or_lambda_map = None
                if isinstance(_expr, Prob) and isinstance(_expr.operand,
                                                          Qcircuit):
                    if _k == 2:
                        # Just a quantum circuit in a probability
                        circuit_or_lambda_map = _expr.operand
                    else:
                        # A portion of a quantum circuit.
                        circuit_or_lambda_map= InnerExpr(
                            _expr, inner_expr.inner_expr_path[-_k+2:])
                    prob_relation_lambda = InnerExpr(
                        expr_hierarchy[0],
                        inner_expr.inner_expr_path[:-_k]).repl_lambda()
                    break
            if circuit_or_lambda_map is None:
                raise NotImplementedError(
                    "Qcircuit.sub_[left/right]_side_into only "
                    "implemented to apply to an inner expr within "
                    "a Prob on a Qcircuit")
            if circuit_or_lambda_map != orig_circuit:
                # Not a direct probability substitution.
                if which_side == 'left':
                    equiv = equiv.derive_reversed()
                    thm = rhs_prob_via_equiv
                equiv = equiv.substitution(circuit_or_lambda_map)
        else:
            # Find Prob(A) for 'right' or Prob(B) for 'left'
            # and make a global replacement.
            if not isinstance(prob_relation_or_inner_expr, Expression):
                raise TypeError(
                    "'prob_relation_or_inner_expr' must be an expression "
                    "involving the Prob of a a quantum circuit or "
                    "an InnerExpr within one")
            orig_prob = Prob(orig_circuit)
            prob_relation_lambda = Lambda.global_repl(
                prob_relation_or_inner_expr, orig_prob)

        # Prove the probability relation.
        return thm.instantiate(
            {Q:prob_relation_lambda, A:equiv.lhs, B:equiv.rhs})

    def sub_left_side_into(self, prob_relation_or_inner_expr, 
                           assumptions=USE_DEFAULTS):
        '''
        Derive a new quantum circuit probability relation from
        another one by substituting the left side of the equivalence
        in place of an occurrence of the right side.
        If specifying a lambda map, it may lambda map for a
        quanutum circuit or portion of one within a probability
        relation.
        '''
        return self._sub_one_side_into(prob_relation_or_inner_expr,
                                       which_side = 'left')

    def sub_right_side_into(self, prob_relation_or_lambda_map, 
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
