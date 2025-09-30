from proveit import (m, n, A, B, C, D,
        defaults, Expression, equality_prover, Judgment, Literal,
        Operation, ExprRange, ProofFailure, prover, relation_prover,
        SimplificationDirectives, TransRelUpdater)
from proveit.logic.booleans import in_bool, Or
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, apply_association_thm,
        apply_disassociation_thm, deduce_equality_via_commutation,
        generic_permutation, group_commutation)

class XOr(Operation):
    '''
    XOr(A, B) represents the logical exclusive or (denoted xor) on
    boolean operands A and B, evaluating to TRUE if and only if A is
    TRUE or B is TRUE but not both. Like the logical Or, XOr is both
    commutative and associative. There is a nice Wikipedia entry
    for XOR at https://en.wikipedia.org/wiki/Exclusive_or .
    This class is under construction by wdc beginning 20250417 using
    the logic/sets/booleans logical Or class as a model.
    '''

    # The operator of the XOr operation
    _operator_ = Literal(
            string_format='xor', latex_format=r'\oplus', theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            ungroup=True)

    # used to avoid infinite recursion inside of unary_reduction
    trivial_xors = set()

    def __init__(self, *operands, styles=None):
        '''
        XOr on any number of operands: A xor B xor ... xor Z
        '''
        Operation.__init__(self, XOr._operator_, operands, styles=styles)
        # deduce trivial disjunctive equivalances with 0 or 1 operand;
        # avoid infinite recursion by storing previously encountered
        # expressions
        if self in XOr.trivial_xors:
            return
        operands = self.operands
        if operands.num_entries() == 0:
            XOr.trivial_xors.add(self)
            try:
                from proveit.logic.booleans.exclusive_disjunction import (
                        empty_xor)
            except BaseException:
                # empty_xor not initially defined when
                # doing a clean rebuild
                pass
        if operands.is_single():
            operand = operands[0]
            try:
                XOr.trivial_xors.add(self)
                in_bool(operand).prove(automation=False)
                self.unary_reduction()
            except BaseException:
                pass

    def _readily_provable(self):
        '''
        Return True iff we should be able to conclude this XOr.
        Unlike the more common Or, which is provable if ANY single
        operand is provable, an XOr requires exactly an odd number
        of its operands to be TRUE for the XOr itself to be TRUE,
        thus an XOr should be provable if exactly an odd number of
        its operands are provable, and the remaining are disprovable.
        '''
        
        from . import (xor_not_if_both, xor_if_only_left,
                       xor_if_only_right, xor_not_if_neither)
        operands = self.operands
        if operands.is_double():
            _A, _B = operands
            provableA = _A.readily_provable()
            provableB = _B.readily_provable()
            disprovableA = _A.readily_disprovable()
            disprovableB = _B.readily_disprovable()

            if (provableA and provableB and xor_not_if_both.is_usable()):
                return False
            if (disprovableA and disprovableB
                and xor_not_if_neither.is_usable()):
                return False
            if (provableA and disprovableB
                and xor_if_only_left.is_usable()):
                return True
            if (disprovableA and provableB
                and xor_if_only_right.is_usable()):
                return True
            return False

        # See Or._readily_provable() in or_op.py for some further
        # existential-related code that might have analogues for
        # the XOr operation.
        
        # The following code block from Or._readily_provable()
        # might be adaptable to the XOr case. Would need to count
        # the readily_provable and readily_disprovable operands,
        # and probably deny cases that involve an ExprRange.
        # for operand in self.operands:
        #     if isinstance(operand, ExprRange):
        #         if Or(operand).readily_provable():
        #             return True
        #     elif operand.readily_provable():
        #         return True
        return False

    def _readily_disprovable(self):
        '''
        Return True iff we should be able to conclude the negation
        of this XOr. For the general case, if exactly an odd number
        of the operands are provable and the rest disprovable, then
        the XOr should be provable. To be disprovable in the general
        case then we would need to show that exactly an even number
        of the operands are provable and the rest disprovable.
        '''
        from . import (xor_not_if_both, xor_if_only_left,
                       xor_if_only_right, xor_not_if_neither)
        operands = self.operands
        if operands.is_double():
            _A, _B = operands
            provableA = _A.readily_provable()
            provableB = _B.readily_provable()
            disprovableA = _A.readily_disprovable()
            disprovableB = _B.readily_disprovable()

            if (provableA and provableB and xor_not_if_both.is_usable()):
                return True
            if (disprovableA and disprovableB
                and xor_not_if_neither.is_usable()):
                return True
            if (provableA and disprovableB
                and xor_if_only_left.is_usable()):
                return False
            if (disprovableA and provableB
                and xor_if_only_right.is_usable()):
                return False
            return False

        # See Or._readily_disprovable() in or_op.py for some further
        # existential-related code that might have analogues for
        # the XOr operation.
        
        # The following code block from Or._readily_provable()
        # might be adaptable to the XOr case. Would need to count
        # the readily_provable and readily_disprovable operands,
        # and probably deny cases that involve an ExprRange.
        for operand in self.operands:
            if isinstance(operand, ExprRange):
                if not Or(operand).readily_disprovable():
                    return False
            elif not operand.readily_disprovable():
                return False
        return False

    # The following helper function from the Or class
    # might be adaptable to the XOr case. Unclear if worth the effort.
    # Leaving here for now as a placeholder.
    # def _as_quantification(self):
    #     '''
    #     If this is a disjunction over a single ExprRange entry,
    #     return the equivalent existential quantification:
    #         P(i) or ... or P(j) <=> exists_{k in {i .. j}} P(k)
    #     '''
    #     from proveit import ExprRange
    #     if (self.operands.num_entries() == 1 and
    #             isinstance(self.operands[0], ExprRange)):
    #         from proveit.logic import Exists
    #         expr_range = self.operands[0]
    #         existential_quant = Exists(
    #                 expr_range.parameter,
    #                 expr_range.body,
    #                 condition = expr_range.parameter_condition())
    #         return existential_quant
    #     return None

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to automatically conclude this XOr. Unlike the simpler Or
        case, we limit the effort to binary (or simpler) cases for now.
        Future development might include a reduction or iterative proof
        for cases with more than 2 operands.
        '''
        # from proveit.logic import And
        from . import true_xor_false, false_xor_true
        if self in {true_xor_false.expr, false_xor_true.expr}:
            # should be proven via one of the imported theorems as a
            # simple special case
            return self.prove()

        if self.operands.is_double():
            # See if we can prove this via the law of the excluded
            # middle.
            from proveit.logic import Not
            _A = self.operands[0]
            _B = self.operands[1]
            _A_cf = _A.canonical_form()
            _B_cf = _B.canonical_form()
            if _B_cf == Not(_A_cf):
                # Prove A or Not(A)
                from proveit.logic.booleans import unfold_is_bool_xor
                replacements = []
                if _B != Not(_A):
                    replacements.append(Not(_A).deduce_canonically_equal(_B))
                return unfold_is_bool_xor.instantiate(
                        {A:_A}, replacements=replacements)
            elif _A_cf == Not(_B_cf):
                # Prove Not(A) or A
                return XOr(_B, _A).prove().inner_expr().commute()

            # can we then check if we know A, Not(B) and use
            # related theorem xor_if_only_left or xor_if_only_right?
            # or is this not appropriate in a conclude() method?

        # OLD from Or; kept temporarily for further development
        # if self.operands.contains_range():
        #     # There are ExprRange operands.
        #     if self.operands.num_entries()==1:
        #         # Just a single ExprRange.
        #         if And(self.operands.entries[0]).readily_provable():
        #             # Trivally, if all of the operands are
        #             # True then any of them are, as long as
        #             # there is at list one (note,
        #             # Or() = FALSE, so we shouldn't try to
        #             # conclude Or() anyway).
        #             return self.conclude_any_via_all()
        #         # Conclude via the equivalent existential 
        #         # quantification.
        #         return self.conclude_over_expr_range()
        #     # Group each ExprRange operand, call conclude_negation,
        #     # then disassociate the ExprRange operands.
        #     return prove_via_grouping_ranges(
        #             self, lambda expr, **kwargs: expr.conclude(**kwargs))
        #
        # for _k, operand in enumerate(self.operands):
        #     if operand.readily_provable():
        #         # With one provable operand, we can prove the 
        #         # disjunction.
        #         return self.conclude_via_example(operand)

        raise ProofFailure(self, defaults.assumptions,
                "XOr.conclude() has failed to find a proof for the "
                "exclusive disjunction: ({})".format(self))

    # not yet clear if this is relevant or correct
    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''
        from proveit.logic import Not
        if self.operands.is_double():
            if self.operands[1] == Not(self.operands[0]):
                # (A xor not(A)) is an unfolded Boolean
                return  # stop to avoid infinite recursion.
        yield self.derive_in_bool

    # Started to adapt this from the Or class, but realized
    # it would have to be modified considerably to apply to XOR.
    # Leaving here as a placeholder for future consideration.
    # def negation_side_effects(self, judgment):
    #     '''
    #     Side-effect derivations to attempt automatically for
    #     Not(A xor B xor .. xor .. Z).
    #     '''
    #     from proveit.logic import Not, And
    #     if self.operands.num_entries() == 0:
    #         return  # No side-effects needed for [XOr]()
    #     if self.operands.is_double():  # Not(A xor B)
    #         # these will need to be updated
    #         yield self.deduce_not_left_if_neither  # Not(A)
    #         yield self.deduce_not_right_if_neither  # Not(B)
    #     # implemented by JML on 7/2/19
    #     # If all of the operands are negated call the conjunction form of
    #     # DeMorgan's
    #     if all(isinstance(operand, Not) for operand in self.operands):
    #         demorgan_and = And(*[operand.operand for operand in self.operands])
    #         yield demorgan_and.conclude_via_demorgans

    def in_bool_side_effects(self, judgment):
        '''
        From (A xor B xor .. xor Z) in Boolean,
        deduce (A in Boolean), (B in Boolean), ... (Z in Boolean).
        '''
        from proveit import ExprRange
        for _i in range(self.operands.num_entries()):
            if not isinstance(self.operands[_i], ExprRange):
                yield lambda : self.deduce_part_in_bool(_i)

    @prover
    def conclude_negation(self, **defaults_config):

        from . import (true_xor_true_negated, false_xor_false_negated,
                       xor_not_if_both, xor_not_if_neither)
        from . import empty_xor
        if self == true_xor_true_negated.operand:
            return true_xor_true_negated # Not(TRUE xor TRUE)
        elif self == false_xor_false_negated.operand:
            return false_xor_false_negated # Not(FALSE xor FALSE)
        elif self.operands.num_entries() == 0:
            return empty_xor
        elif self.operands.is_double():
            try:
                return xor_not_if_both.instantiate(
                        {A: self.operands[0], B: self.operands[1]})
            except Exception as the_exception:
                return xor_not_if_neither.instantiate(
                        {A: self.operands[0], B: self.operands[1]})
        else:
            _A_sub = self.operands
            _m_sub = _A_sub.num_elements()
            # Here we turn auto_simplification off because Prove-It
            # knows that Not(A) is TRUE, and as a result it would
            # simplify A to FALSE during auto_simplification:
            return not_xor_if_not_any.instantiate(
                    {m:_m_sub, A:_A_sub}, auto_simplify=False)

    @prover
    def conclude_via_only_left(self, **defaults_config):
        from . import xor_if_only_left
        assert self.operands.is_double()
        return xor_if_only_left.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_only_right(self, **defaults_config):
        from . import xor_if_only_right
        assert self.operands.is_double()
        return xor_if_only_right.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    def _build_canonical_form(self):
        '''
        Returns a form of this XOr operation in which the operands are 
        in a deterministically sorted order used to determine equal 
        expressions given commutativity of this operation under
        appropriate conditions.
        '''
        return XOr(*sorted([operand.canonical_form() for operand 
                          in self.operands.entries], key=hash))

    def _deduce_canonically_equal(self, rhs):
        from proveit.logic import Equals
        equality = Equals(self, rhs)
        return deduce_equality_via_commutation(equality, one_side=self)

    @prover
    def derive_right_if_not_left(self, **defaults_config):
        '''
        From (A xor B) derive and return B assuming Not(A), in_bool(B).
        '''
        from . import right_if_not_left
        assert self.operands.is_double
        left_operand, right_operand = self.operands
        return right_if_not_left.instantiate(
            {A: left_operand, B: right_operand})

    @prover
    def derive_left_if_not_right(self, **defaults_config):
        '''
        From (A xor B) derive and return A assuming in_bool(A), Not(B).
        '''
        from . import left_if_not_right
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return left_if_not_right.instantiate(
            {A: left_operand, B: right_operand})

    @prover
    def derive_not_right_if_left(self, **defaults_config):
        '''
        From (A xor B) and knowing or assuming A and in_bool(A),
        derive Not(B).
        '''
        from . import not_right_if_left
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return not_right_if_left.instantiate(
                {A: left_operand, B: right_operand})

    @prover
    def derive_not_left_if_right(self, **defaults_config):
        '''
        From (A xor B) and knowing or assuming B and in_bool(B),
        derive Not(A).
        '''
        from . import not_left_if_right
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return not_left_if_right.instantiate(
                {A: left_operand, B: right_operand})

    @prover
    def derive_via_singular_dilemma(self, conclusion, **defaults_config):
        '''
        From (A xor B) as self, and assuming A => C, B => C, and
        A and B are Boolean, derive and return the conclusion, C.
        '''
        from . import (singular_constructive_dilemma,
                       singular_constructive_multi_dilemma)
        if self.operands.is_double():
            return singular_constructive_dilemma.instantiate(
                {A: self.operands[0], B: self.operands[1], C: conclusion},
                preserve_expr=conclusion)
        _A_sub = self.operands
        _m_sub = _A_sub.num_elements()
        return singular_constructive_multi_dilemma.instantiate(
                {m: _m_sub, A: _A_sub, C: conclusion}, preserve_expr=conclusion)

    @prover
    def derive_via_multi_dilemma(self, conclusion, **defaults_config):
        '''
        From (A xor B) as self, and assuming A => C, B => D, and
        A, B, C, and D are Boolean, derive and return the conclusion,
        (C V D). Multiple variants are considered.
        '''
        from . import (constructive_dilemma, destructive_dilemma,
                       constructive_multi_dilemma, destructive_multi_dilemma)
        from proveit.logic import Not, Or
        from proveit import ExprTuple
        assert (isinstance(conclusion, Or) and
                (conclusion.operands.num_entries()
                == self.operands.num_entries())), \
                ("derive_via_multi_dilemma requires conclusion to be a "
                 "disjunction (Or), with the same number of "
                 "operands as self.")
        with defaults.temporary() as temp_defaults:
            # temp_defaults.preserve_expr(conclusion)
            temp_defaults.preserved_exprs = (
                    defaults.preserved_exprs.union([conclusion]))
            # Check for destructive versus constructive dilemma cases.
            if (all(isinstance(operand, Not) for operand in self.operands)
               and
               all(isinstance(operand, Not) for operand in conclusion.operands)
               ):
                # destructive case.
                if (self.operands.is_double()
                    and destructive_dilemma.is_usable()):
                    # From Not(C) xor Not(D), A => C, B => D, conclude
                    # Not(A) xor Not(B)
                    return destructive_dilemma.instantiate(
                        {C: self.operands[0].operand,
                         D: self.operands[1].operand,
                         A: conclusion.operands[0].operand,
                         B: conclusion.operands[1].operand})
                elif destructive_multi_dilemma.is_usable():
                    # raise NotImplementedError("Generalized destructive
                    # multi-dilemma not implemented yet.")
                    # Iterated destructive case.
                    # From (Not(A) xor Not(B) xor Not(C)
                    # xor Not(D)) as self
                    negated_operands_self = [
                        operand.operand for operand in self.operands]
                    negated_operands_conc = [
                        operand.operand for operand in conclusion.operands]
                    _A = ExprTuple(*negated_operands_conc)
                    _B = ExprTuple(*negated_operands_self)
                    _m = _A.num_elements()
                    return destructive_multi_dilemma.instantiate(
                            {m: _m, A: _A, B: _B})
            # constructive case.
            if self.operands.is_double():
                # From (A xor B), A => C, B => D, conclude (C V D).
                return constructive_dilemma.instantiate(
                    {A: self.operands[0],
                     B: self.operands[1],
                     C: conclusion.operands[0],
                     D: conclusion.operands[1]})

            _A = self.operands
            _B = conclusion.operands
            _m = _A.num_elements()
            return constructive_multi_dilemma.instantiate(
                    {m: _m, A: _A, B: _B})

    @prover
    def derive_via_dilemma(self, conclusion, **defaults_config):
        '''
        If the conclusion is an Or operation with the same number
        of operands as self, try derive_via_multi_dilemma.  Otherwise,
        or if that fails, try derive_via_singular_dilemma.
        '''
        if (isinstance(conclusion, Or) and
                (conclusion.operands.num_entries() ==
                 self.operands.num_entries())):
            try:
                return self.derive_via_multi_dilemma(conclusion)
            except ProofFailure:
                pass
        return self.derive_via_singular_dilemma(conclusion)

    @prover
    def deduce_left_in_bool(self, **defaults_config):
        '''
        Deduce A in Boolean from (A xor B) in Boolean.
        '''
        from . import left_in_bool
        if self.operands.is_double():
            return left_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})

    @prover
    def deduce_right_in_bool(self, **defaults_config):
        '''
        Deduce B in Boolean from (A xor B) in Boolean.
        '''
        from . import right_in_bool
        if self.operands.is_double():
            return right_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})

    @prover
    def deduce_part_in_bool(self, index_or_expr, **defaults_config):
        '''
        Deduce X in Boolean from (A xor B xor .. xor X xor .. xor Z)
        in Boolean, specifying X by expression or index number.
        '''
        from . import each_is_bool
        idx = index_or_expr if isinstance(
            index_or_expr, int) else list(
            self.operands).index(index_or_expr)
        if idx < 0 or idx >= self.operands.num_entries():
            raise IndexError("Operand out of range: " + str(idx))
        if self.operands.is_double():
            if idx == 0:
                return self.deduce_left_in_bool()
            elif idx == 1:
                return self.deduce_right_in_bool()
        _A_sub, _B_sub, _C_sub = (
            self.operands[:idx], self.operands[idx],self.operands[idx + 1:])
        _m_sub = _A_sub.num_elements()
        _n_sub = _C_sub.num_elements()
        return each_is_bool.instantiate(
                {m: _m_sub, n: _n_sub, A: _A_sub, B: _B_sub, C: _C_sub})

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        IN DEVELOPMENT, BASED ON DISJUNCTION Or.
        Attempt to determine whether this XOr, with
        simplified operands, evaluates to TRUE or FALSE under the
        given assumptions.  If all operands have simplified to FALSE,
        the disjunction is FALSE. If exactly one of two operands has
        simplified to TRUE and the other FALSE, the XOr is TRUE.
        More generally, an XOr is TRUE if exactly an odd number of
        its operands are TRUE and the rest are FALSE. (This is
        considerably more troublesome than the more common inclusive
        disjunction Or.)
        If it can't be evaluated, and must_evaluate is False,
        ungroup nested disjunctions if that is an active
        simplification direction.  Also, if applicable, perform
        a unary reduction: XOr(A) = A.
        '''
        from proveit.logic import (Equals, FALSE, TRUE, EvaluationError,
                                   is_irreducible_value)
        # load in truth-table evaluations
        from . import (xor_t_t, xor_t_f, xor_f_t, xor_f_f)
        if self.operands.num_entries() == 0:
            from proveit.logic.booleans.exclusive_disjunction import (
                    empty_xor_eval)
            # XOr() = FALSE
            return empty_xor_eval

        # Check whether or not all of the operands are FALSE
        # or any are TRUE.
        all_are_false = True
        _num_true_ops = 0
        _num_false_ops = self.operands.num_entries()
        for operand in self.operands:
            if operand != FALSE:
                all_are_false = False
                _num_false_ops -= 1
            if operand == TRUE:
                _num_true_ops += 1
            # if operand == TRUE:
            #     # If any simplified operand is TRUE, the disjunction
            #     # may only evaluate to TRUE if it can be evaluated.
            #     # Only use automation here if 'must_evaluate' is True.
            #     self.conclude(automation=must_evaluate)
            #     return Equals(self, TRUE).prove()

        # If binary and both operands evaluate to TRUE or FALSE
        # we should be able to prove a simplification
        if (self.operands.is_double()
            and _num_true_ops + _num_false_ops == 2):
            if (all_are_false or _num_true_ops == 2):
                self.conclude_negation()
                return Equals(self, FALSE).prove()
            else:
                self.conclude()
                return Equals(self, TRUE).prove()

        # If we are not dealing with 2 operands but all of the
        # operands are FALSE, we can still prove that the XOr is
        # equal to FALSE.
        if all_are_false:
            self.conclude_negation()
            return Equals(self, FALSE).prove()

        # EVENTUALLY should be able to prove TRUE if we have an
        # odd number of TRUE operands with the remainder all FALSE
        # if ((_num_true_ops % 2 == 1)
        #     and _num_true_ops + _num_false_ops == self.operands.num_entries()):
        #     # call some relevant method here that will use some
        #     # yet-to-be created theorem

        if must_evaluate:
            # FROM the Or method; not yet clear how to appy to XOr
            # if self.operands.contains_range():
            #     if self.operands.num_entries() == 1:
            #         # Disjunction of a single ExprRange.  Convert to an
            #         # existential quantification and evaluate that.
            #         expr_range = self.operands[0]
            #         _i = expr_range.true_start_index
            #         _j = expr_range.true_end_index
            #         _P = expr_range.lambda_map
            #         conj_eq_quant = (disjunction_eq_quantification
            #                          .instantiate({i:_i, j:_j, P:_P},
            #                                       preserve_all=True))
            #         return conj_eq_quant.apply_transitivity(
            #                 conj_eq_quant.rhs.evaluation())
            #     return prove_via_grouping_ranges(
            #             self, lambda expr, **kwargs: expr.evaluation(**kwargs))
            if not all(is_irreducible_value(operand) for
                       operand in self.operands):
                # The simplification of the operands may not have
                # worked hard enough.  Let's work harder if we
                # must evaluate.
                for operand in self.operands:
                    if not is_irreducible_value(operand):
                        temp_result = operand.evaluation()
                return self.evaluation()
            # Can't evaluate the XOr if not all operands are FALSE
            # but we also don't have exactly an odd number TRUE.
            raise EvaluationError(self)

        if self.operands.is_single():
            # XOr(A) = A
            return self.unary_reduction()

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        if XOr._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested disjunctions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                if isinstance(operand, XOr):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, auto_simplify=False))
                length = expr.operands.num_entries()
                _n += 1

        return Expression.shallow_simplification(self)

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From (A xor B), and (1) knowing or assuming not(A) and not(B),
        derive and return FALSE; or (2) knowing or assuming A and B,
        derive and return FALSE. The disjunction Or version of this
        method also deals with cases of more than 2 operands, but the
        XOr case does not.
        '''
        from . import (binary_xor_neither_contradiction,
                       binary_xor_both_contradiction)
        from proveit.logic import FALSE, TRUE
        
        if self.operands.is_double():
            _A_sub = self.operands[0]
            _B_sub = self.operands[1]
            if (_A_sub.readily_disprovable() and _B_sub.readily_disprovable()):
                return binary_xor_neither_contradiction.instantiate(
                    {A: _A_sub, B: _B_sub})
            # if (_A_sub == FALSE and _B_sub == FALSE):
            #     return binary_xor_neither_contradiction.instantiate(
            #         {A: _A_sub, B: _B_sub})
            elif (_A_sub.readily_provable() and _B_sub.readily_provable()):
                return binary_xor_both_contradiction.instantiate(
                    {A: _A_sub, B: _B_sub})
            else:
                raise NotImplementedError("'derive_contradiction() "
                        f"not implemented for {self}")
        else:
            raise NotImplementedError("'derive_contradiction() "
                    f"not implemented for non-binary case: {self}.")

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From (A xor B), derive the conclusion, provided that the
        negated conclusion implies not(A xor B), and the conclusion is a
        Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''

        From (A xor B), derive the negated conclusion provided that the
        conclusion implies not(A xor B), and the conclusion
        is a Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion)

    def readily_in_bool(self):
        '''
        Returns True if we can readily prove that all of the operands
        are provably boolean and therefore this exclusive disjunction
        XOr is provably boolean. As in the Or case, we re-use the
        readily_in_bool() method of the conjunction (And) class.
        '''
        from . import closure
        from proveit.logic import And
        if not self.operands.is_double() and not closure.is_usable():
            return False
        # The requirement for a conjunction is the same for a 
        # disjunction (Or or XOr) -- all operands must be provably
        # boolean.
        return And.readily_in_bool(self)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this 'xor' expression
        is in the set of BOOLEANS.
        '''
        from . import binary_closure, closure
        if self.operands.is_double():
            return binary_closure.instantiate(
                {A: self.operands[0], B: self.operands[1]},
                preserve_expr=self)
        else:
            _A_sub = self.operands
            _m_sub = _A_sub.num_elements()
            return closure.instantiate(
                {m: _m_sub, A: _A_sub}, preserve_expr=self)

    @prover
    def conclude_via_permutation(self, permuted_xor, **defaults_config):
        '''
        From some true (or assumed true) but permutated version of this
        XOr expression, conclude that this XOr expression is true.
        For example, let this_xor = A xor B xor C xor D
        and let perm_of_this_xor = S |- B xor A xor C xor D.
        From perm_of_this_xor, conclude this_xor, using the following:

            this_xor.conclude_via_permuation(
                    perm_of_this_xor, assumptions = S),

        which will return S |– A xor B xor C xor D.

        '''

        # Check that the permuted_xor is an instance of XOr. Need to
        # distinguish between Judgment and Expression versions of the
        # provided permuted_xor.
        if isinstance(permuted_xor, Judgment):
            perm_xor_expr = permuted_xor.expr
        else:
            perm_xor_expr = permuted_xor
        if not isinstance(perm_xor_expr, XOr):
            raise TypeError('permuted_xor arg should be an exclusive '
                            'disjunction (XOr) Expression or Judgment '
                            'but instead was {permuted_xor}.')

        # Check that each of the operands in permuted_xor occur as
        # operands in self (and vice-versa), otherwise throw a
        # ValueError.
        self_operands = self.operands
        perm_operands = permuted_xor.operands
        unexpected_operands = (
            set(self_operands).symmetric_difference(set(perm_operands)))
        if len(unexpected_operands) != 0:
            raise ValueError(
                    f"The original expression: {self}, and the provided "
                    f"permutated XOr: {permuted_xor}, differ, with "
                    f"unexpected item(s): {unexpected_operands}.")

        # NOTICE that we are assuming no repetition of operands and
        # that len(perm_operands) = self_operands.num_entries()

        for _i in range(self_operands.num_entries()):
            # update the operands list each time for the
            # permuting version
            perm_operands = permuted_xor.operands
            temp_operand = self_operands[_i]
            _j = perm_operands.index(temp_operand)
            equiv_permuted_xor = (
                permuted_xor.commutation(_j, _i)
            )
            permuted_xor = (
                equiv_permuted_xor
                .sub_right_side_into(permuted_xor)
            )

        return permuted_xor

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        '''
        For the degenerate case of XOr(A), where A is Boolean, derive
        and return |–[xor](A) = A. For example, calling
            XOr(A).unary_reduction([in_bool(A)])
        will return:
            {A in Bool} |– [xor](A) = A
        '''
        from proveit.logic.booleans.exclusive_disjunction import (
            unary_xor_reduction)
        if not self.operands.is_single():
            raise ValueError(
                    "XOr.unary_reduction(): expression must have only a "
                    "single operand in order to invoke the "
                    "unary_or_reduction theorem.")
        operand = self.operands[0]
        return unary_xor_reduction.instantiate({A: operand})

    @equality_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal
        to a form in which the operand at index init_idx has been
        moved to final_idx. For example,

          (A xor B xor ... xor Y xor Z) = (A xor ... xor Y xor B xor Z)

        via init_idx = 1 (for 'B') and final_idx = -2.
        '''

        from . import (commutation, leftward_commutation,
                       rightward_commutation)
        return apply_commutation_thm(
            self, init_idx, final_idx, commutation,
            leftward_commutation, rightward_commutation)

    @equality_prover('group_commuted', 'group_commute')
    def group_commutation(self, init_idx, final_idx, length,
                          disassociate=True, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal
        to a form in which the operands at indices
        [init_idx, init_idx+length) have been moved to
        [final_idx, final_idx+length). It will do this by performing
        association first. If disassociate is True, it will be
        disassociated afterward. For example, the call
        XOr(A,B,C,D).group_commutation(0, 1, length=2,
                                 assumptions=in_bool(A,B,C,D))
        will conceptually follow the steps:
        (1) associates 2 elements (i.e. length = 2) starting at index 0
            to obtain (A V B) V C V D
        (2) removes the element to be commuted to obtain C V D
        (3) inserts the element to be commuted at the desire index 1 to
            obtain C V (A V B) V D
        (4) then disassociates to obtain C V A V B V D
        (5) eventually producing the output:
            {A in Bool, ..., D in Bool} |-
            (A V B V C V D) = (C V A V B V D)
        '''
        return group_commutation(
            self, init_idx, final_idx, length, disassociate)

    @equality_prover('moved', 'move')
    def permutation_move(self, init_idx=None, final_idx=None,
                         **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal 
        to a form in which the operand at index init_idx has been
        moved to final_idx. For example,

          (a xor b xor ... xor y xor z) = (a xor ... xor y xor b xor z)

        via init_idx = 1 (for the 'b') and final_idx = -2.
        '''

        return self.commutation(init_idx=init_idx, final_idx=final_idx)

    @equality_prover('permuted', 'permute')
    def permutation(self, new_order=None, cycles=None, **defaults_config):
        '''
        Deduce that this XOr expression is equal to an XOr in which
        the terms at indices 0, 1, …, n-1 have been reordered as
        specified EITHER by the new_order list OR by the cycles list
        parameter. For example,

            (a xor b xor c xor d).permutation(new_order=[0, 2, 3, 1])
        and
            (a xor b xor c xor d).permutation(cycles=[(1, 2, 3)])

        would both return

            |- (a xor b xor c xor d) = (a xor c xor d xor d).
        '''
        return generic_permutation(self, new_order, cycles)

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal
        to a form in which operands in the range
            [start_idx, start_idx+length)
        are grouped together. For example,
        (A or B or ... or Y or Z) =
        (A or B ... or (L or ... or M) or ... or Y or Z)
        '''
        from . import association
        return apply_association_thm(
            self, start_idx, length, association)

    @prover
    def associate(self, start_idx, length, **defaults_config):
        '''
        From self, derive and return a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, from (A xor B xor ... xor Y xor Z) derive
        (A xor B ... xor (L xor ... xor M) xor ... xor Y xor Z).
        '''
        from . import associate
        return apply_association_thm(
            self, start_idx, length, associate)

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to
        a form in which the operand at index idx is no longer grouped
        together.
        For example,
            (A or B ... or (L or ... or M) or ... or Y or Z) =
            (A or B or ... or Y or Z)
        '''
        from . import disassociation
        return apply_disassociation_thm(self, idx, disassociation)

    @prover
    def disassociate(self, idx, **defaults_config):
        '''
        From self, derive and return a form in which the operand
        at the given index is ungrouped.
        For example, from
            (A xor B ... xor (L xor ... xor M) xor ... xor Y xor Z)
        derive (A xor B xor ... xor Y xor Z).
        '''
        from . import disassociate
        return apply_disassociation_thm(self, idx, disassociate)
