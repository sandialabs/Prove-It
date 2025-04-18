from proveit import (A, B, C,
        defaults, equality_prover, Literal, Operation, ProofFailure,
        prover, SimplificationDirectives)
from proveit.logic.booleans import in_bool

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
        if self in {true_xor_false, false_xor_true}:
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
                from proveit.logic.booleans import unfold_is_bool
                replacements = []
                if _B != Not(_A):
                    replacements.append(Not(_A).deduce_canonically_equal(_B))
                return unfold_is_bool.instantiate(
                        {A:_A}, replacements=replacements)
            elif _A_cf == Not(_B_cf):
                # Prove Not(A) or A
                return Or(_B, _A).prove().inner_expr().commute()

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
                "Or.conclude() has failed to find a proof for the "
                "exclusive disjunction: ({})".format(self))

    # not yet clear if this is relevant or correct
    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''
        from proveit.logic import Not
        if self.operands.is_double():
            if self.operands[1] == Not(self.operands[0]):
                # (A or not(A)) is an unfolded Boolean
                return  # stop to avoid infinite recursion.
        yield self.derive_in_bool

    # not yet clear if this is relevant or correct
    # commented out until further updates to deduce_not_left_if_neither,
    # etc., in code block
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

    # not clear if this will eventually work; commenting out until
    # we have the deduce_part_in_bool() method
    # def in_bool_side_effects(self, judgment):
    #     '''
    #     From (A xor B xor .. xor Z) in Boolean,
    #     deduce (A in Boolean), (B in Boolean), ... (Z in Boolean).
    #     '''
    #     from proveit import ExprRange
    #     for _i in range(self.operands.num_entries()):
    #         if not isinstance(self.operands[_i], ExprRange):
    #             yield lambda : self.deduce_part_in_bool(_i)

    @prover
    def conclude_negation(self, **defaults_config):
        # NEW

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

    # Not relevant for XOr; delete
    # @prover
    # def conclude_via_both(self, **defaults_config):
    #     from . import or_if_both
    #     assert self.operands.is_double()
    #     return or_if_both.instantiate(
    #         {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_only_left(self, **defaults_config):
        from . import xor_if_only_left
        assert self.operands.is_double()
        return xor_if_only_left.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    # Not relevant for XOr; delete
    # @prover
    # def conclude_via_left(self, **defaults_config):
    #     '''
    #     From A being (or assumed) True, conclude that (A V B) is True.
    #     '''
    #     from . import or_if_left
    #     assert self.operands.is_double()
    #     return or_if_left.instantiate(
    #         {A: self.operands[0], B: self.operands[1]})

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

    # this one doesn't yet work
    def _deduce_canonically_equal(self, rhs):
        from proveit.logic import Equals
        equality = Equals(self, rhs)
        return deduce_equality_via_commutation(equality, one_side=self)

    # WORKING HERE

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

    # WORKING HERE

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
            unary_or_reduction)
        if not self.operands.is_single():
            raise ValueError(
                    "XOr.unary_reduction(): expression must have only a "
                    "single operand in order to invoke the "
                    "unary_or_reduction theorem.")
        operand = self.operands[0]
        return unary_or_reduction.instantiate({A: operand})
