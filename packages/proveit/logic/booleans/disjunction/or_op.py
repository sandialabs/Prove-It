from proveit import (Expression, Literal, Operation, defaults, USE_DEFAULTS,
                     ProofFailure, InnerExpr, UnusableProof,
                     prover, equality_prover, SimplificationDirectives, TransRelUpdater)
from proveit import A, B, C, D, m, n
from proveit.logic.booleans.booleans import in_bool
from proveit.abstract_algebra.generic_methods import (apply_commutation_thm, apply_association_thm,
    apply_disassociation_thm, group_commutation, group_commute)


class Or(Operation):
    # The operator of the Or operation
    _operator_ = Literal(
        string_format='or',
        latex_format=r'\lor',
        theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
        ungroup=True)

    # used to avoid infinite recursion inside of unary_reduction
    trivial_disjunctions = set()

    def __init__(self, *operands, styles=None):
        '''
        Or together any number of operands: A or B or C
        '''
        Operation.__init__(self, Or._operator_, operands, styles=None)
        # deduce trivial disjunctive equivalances with 0 or 1 operand
        # avoid infinite recursion by storing previously encountered
        # expressions
        if self in Or.trivial_disjunctions:
            return
        operands = self.operands
        if operands.num_entries() == 0:
            Or.trivial_disjunctions.add(self)
            try:
                from proveit.logic.booleans.disjunction import empty_disjunction
            except BaseException:
                pass  # empty_disjunction not initially defined when doing a clean rebuild
        if operands.is_single():
            operand = operands[0]
            try:
                Or.trivial_disjunctions.add(self)
                in_bool(operand).prove(automation=False)
                self.unary_reduction()
            except BaseException:
                pass

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to automatically conclude this disjunction.  If any of its
        operands have pre-existing proofs, it will be proven via the
        or_if_any theorem.  Otherwise, a reduction proof will be
        attempted (evaluating the operands).
        '''
        from . import true_or_true, true_or_false, false_or_true
        if self in {true_or_true.expr, true_or_false.expr, false_or_true.expr}:
            # should be proven via one of the imported theorems as a 
            # simple special case
            return self.prove()
        # Prove that the disjunction is true by proving that ANY of its
        # operands is true.   In the first attempt, don't use automation
        # to prove any of the operands so that  we don't waste time 
        # trying to prove operands when we already know one to be true.
        for use_automation_for_operand in [False, True]:
            proven_operand_indices = []
            for _k, operand in enumerate(self.operands):
                try:
                    operand.prove(automation=use_automation_for_operand)
                    proven_operand_indices.append(_k)
                    # possible way to prove it:
                    self.conclude_via_example(operand)
                except ProofFailure:
                    pass
            if self.operands.is_double() and len(proven_operand_indices) > 0:
                # One or both of the two operands were known to be true 
                # (without automation).   Try a possibly simpler proof 
                # than conclude_via_example.
                try:
                    if len(proven_operand_indices) == 2:
                        return self.conclude_via_both()
                    elif proven_operand_indices[0] == 0:
                        return self.conclude_via_only_left()
                    else:
                        return self.conclude_via_only_right()
                except BaseException:
                    pass
            if len(proven_operand_indices) > 0:
                try:
                    # proven using conclude_via_example above 
                    # (unless or_if[Any,Left,Right] was not a usable theorem,
                    # in which case this will fail and we can simply try the
                    # default below)
                    return self.prove(automation=False)
                except UnusableProof:
                    # or_if[Any,Left,Right] must not have been a usable
                    # theorem; use the default below.
                    break

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

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for Not(A or B or .. or .. Z).
        '''
        from proveit.logic import Not, And
        if self.operands.num_entries() == 0:
            return  # No side-effects needed for [Or]()
        yield self.derive_in_bool  # A or B or .. or .. Z in Boolean
        if self.operands.is_double():  # Not(A or B)
            yield self.deduce_not_left_if_neither  # Not(A)
            yield self.deduce_not_right_if_neither  # Not(B)
        # implemented by JML on 7/2/19
        # If all of the operands are negated call the conjunction form of
        # DeMorgan's
        if all(isinstance(operand, Not) for operand in self.operands):
            demorgan_and = And(*[operand.operand for operand in self.operands])
            yield demorgan_and.conclude_via_demorgans

    def in_bool_side_effects(self, judgment):
        '''
        From (A or B or .. or Z) in Boolean deduce (A in Boolean), (B in Boolean), ...
        (Z in Boolean).
        '''
        for _i in range(self.operands.num_entries()):
            yield lambda : self.deduce_part_in_bool(_i)

    @prover
    def conclude_negation(self, **defaults_config):
        from . import false_or_false_negated, neither_intro, not_or_if_not_any
        from . import empty_disjunction
        if self == false_or_false_negated.operand:
            return false_or_false_negated  # the negation of (FALSE or FALSE)
        elif self.operands.num_entries() == 0:
            return empty_disjunction
        elif self.operands.is_double():
            return neither_intro.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        else:
            _A = self.operands
            _m = _A.num_elements()
            return not_or_if_not_any.instantiate({m: _m, A: _A}, preserve_all=True)#auto_simplify=False)
            # we turn auto_simplification off because proveit knows that Not(A) is true,
            # as a result, it simplifies A to be False during auto_simplification

    @prover
    def conclude_via_both(self, **defaults_config):
        from . import or_if_both
        assert self.operands.is_double()
        return or_if_both.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_only_left(self, **defaults_config):
        from . import or_if_only_left
        assert self.operands.is_double()
        return or_if_only_left.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_left(self, **defaults_config):
        '''
        From A being (or assumed) True, conclude that (A V B) is True.
        '''
        from . import or_if_left
        assert self.operands.is_double()
        return or_if_left.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_only_right(self, **defaults_config):
        from . import or_if_only_right
        assert self.operands.is_double()
        return or_if_only_right.instantiate(
            {A: self.operands[0], B: self.operands[1]})

    @prover
    def conclude_via_demorgans(self, **defaults_config):
        '''
        # created by JML 6/28/19
        From A and B and C conclude Not(Not(A) or Not(B) or Not(C))
        '''
        from . import demorgans_law_and_to_or, demorgans_law_and_to_or_bin
        if self.operands.is_double():
            return demorgans_law_and_to_or_bin.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        else:
            _A = self.operands
            _m = _A.num_elements()
            return demorgans_law_and_to_or.instantiate({m: _m, A: _A})

    @prover
    def derive_in_bool(self, **defaults_config):
        '''
        From (A or B or ... or Z) derive [(A or B or ... or Z) in Boolean].
        '''
        return in_bool(self).prove()

    @prover
    def derive_right_if_not_left(self, **defaults_config):
        '''
        From (A or B) derive and return B assuming Not(A), in_bool(B).
        '''
        from . import right_if_not_left
        assert self.operands.is_double
        left_operand, right_operand = self.operands
        return right_if_not_left.instantiate(
            {A: left_operand, B: right_operand})

    @prover
    def derive_left_if_not_right(self, **defaults_config):
        '''
        From (A or B) derive and return A assuming in_bool(A), Not(B).
        '''
        from . import left_if_not_right
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return left_if_not_right.instantiate(
            {A: left_operand, B: right_operand})

    @prover
    def derive_via_singular_dilemma(self, conclusion, **defaults_config):
        '''
        From (A or B) as self, and assuming A => C, B => C, and A and B 
        are Boolean, derive and return the conclusion, C.
        '''
        from . import (singular_constructive_dilemma,
                       singular_constructive_multi_dilemma)
        if self.operands.is_double():
            return singular_constructive_dilemma.instantiate(
                {A: self.operands[0], B: self.operands[1], C: conclusion},
                preserve_expr=conclusion)
        _A = self.operands
        _m = _A.num_elements()
        return singular_constructive_multi_dilemma.instantiate(
                {m: _m, A: _A, C: conclusion}, preserve_expr=conclusion)

    @prover
    def derive_via_multi_dilemma(self, conclusion, **defaults_config):
        '''
        From (A or B) as self, and assuming A => C, B => D, and 
        A, B, C, and D are Boolean, derive and return the conclusion,
        C or D.
        '''
        from . import (constructive_dilemma, destructive_dilemma, 
                       constructive_multi_dilemma, destructive_multi_dilemma)
        from proveit.logic import Not, Or
        from proveit import ExprTuple
        assert (isinstance(conclusion, Or) and 
                (conclusion.operands.num_entries() 
                == self.operands.num_entries())), \
                ("derive_via_multi_dilemma requires conclusion to be a "
                 "disjunction, the same number of operands as self.")
        with defaults.temporary() as temp_defaults:
            # temp_defaults.preserve_expr(conclusion)
            temp_defaults.preserved_exprs = defaults.preserved_exprs.union([conclusion])
            # Check for destructive versus constructive dilemma cases.
            if all(isinstance(operand, Not) for operand in self.operands) and all(
                    isinstance(operand, Not) for operand in conclusion.operands):
                # destructive case.
                if self.operands.is_double() and destructive_dilemma.is_usable():
                    # From Not(C) or Not(D), A => C, B => D, conclude 
                    # Not(A) or Not(B)
                    return destructive_dilemma.instantiate(
                        {C: self.operands[0].operand,
                         D: self.operands[1].operand,
                         A: conclusion.operands[0].operand,
                         B: conclusion.operands[1].operand})
                elif destructive_multi_dilemma.is_usable():
                    # raise NotImplementedError("Generalized destructive
                    # multi-dilemma not implemented yet.")
                    # Iterated destructive case. 
                    # From (Not(A) or Not(B) or Not(C)
                    # or Not(D)) as self
                    negated_operands_self = [
                        operand.operand for operand in self.operands]
                    negated_operands_conc = [
                        operand.operand for operand in conclusion.operands]
                    _A = ExprTuple(*negated_operands_self)
                    _B = ExprTuple(*negated_operands_conc)
                    _m = _A.num_elements()
                    return destructive_multi_dilemma.instantiate(
                            {m: _m, A: _A, B: _B})
            # constructive case.
            if self.operands.is_double():
                # From (A or B), A => C, B => D, conclude C or D.
                return constructive_dilemma.instantiate(
                    {A: self.operands[0],
                     B: self.operands[1],
                     C: conclusion.operands[0],
                     D: conclusion.operands[1]})
            #raise NotImplementedError("Generalized constructive multi-dilemma not implemented yet.")
            _A = self.operands
            _B = conclusion.operands
            _m = _A.num_elements()
            return constructive_multi_dilemma.instantiate(
                    {m: _m, A: _A, B: _B})

    @prover
    def derive_via_dilemma(self, conclusion, **defaults_config):
        '''
        If the conclusion is also an Or operation with the same number of operands as
        self, try derive_via_multi_dilemma.  Otherwise, or if that fails, try
        derive_via_singular_dilemma.
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
        Deduce A in Boolean from (A or B) in Boolean.
        '''
        from . import left_in_bool
        if self.operands.is_double():
            return left_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})

    @prover
    def deduce_right_in_bool(self, **defaults_config):
        '''
        Deduce B in Boolean from (A or B) in Boolean.
        '''
        from . import right_in_bool
        if self.operands.is_double():
            return right_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})

    @prover
    def deduce_part_in_bool(self, index_or_expr, **defaults_config):
        '''
        Deduce X in Boolean from (A or B or .. or X or .. or Z) in Boolean
        provided X by expression or index number.
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
        _A, _B, _C = (self.operands[:idx], self.operands[idx], 
                      self.operands[idx + 1:])
        _m = _A.num_elements()
        _n = _C.num_elements()
        return each_is_bool.instantiate(
                {m: _m, n: _n, A: _A, B: _B, C: _C})

    @prover
    def deduce_not_left_if_neither(self, **defaults_config):
        '''
        Deduce not(A) assuming not(A or B) where self is (A or B).
        '''
        from . import not_left_if_neither
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return not_left_if_neither.instantiate(
            {A: left_operand, B: right_operand})

    @prover
    def deduce_not_right_if_neither(self, **defaults_config):
        '''
        Deduce not(B) assuming not(A or B) where self is (A or B).
        '''
        from . import not_right_if_neither
        assert self.operands.is_double()
        left_operand, right_operand = self.operands
        return not_right_if_neither.instantiate(
            {A: left_operand, B: right_operand})

    @equality_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Attempt to determine whether this disjunction, with
        simplified operands, evaluates to TRUE or FALSE under the given 
        assumptions.  If all operands have simplified to FALSE,
        the disjunction is FALSE.  If any of the operands have
        simplified to TRUE, the disjunction is TRUE (if the
        other operands are provably Boolean).
        '''
        from proveit.logic import Equals, FALSE, TRUE, EvaluationError
        # load in truth-table evaluations
        from . import or_t_t, or_t_f, or_f_t, or_f_f
        if self.operands.num_entries() == 0:
            from proveit.logic.booleans.disjunction import \
                empty_disjunction_eval
            # And() = TRUE
            return empty_disjunction_eval
        
        all_are_false = True
        for operand in self.operands:
            if operand != FALSE:
                all_are_false = False
            if operand == TRUE:
                # If any simplified operand is FALSE, the conjunction 
                # may only evaluate to FALSE if it can be evaluated.
                self.prove()
                return Equals(self, TRUE).prove()
        # If no simplified operand is FALSE, it may only evaluate to
        # FALSE if it can be evaluated.
        if not all_are_false:
            # Can't evaluate the disjunction if no operand was
            # TRUE but they aren't all FALSE.
            raise EvaluationError(self)
        self.disprove()
        return Equals(self, FALSE).prove()

    """
    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        Attempt to determine whether this disjunction evaluates
        to true or false under the given assumptions.  If automation
        is false, it will only succeed if the evaluation is already
        known.  If automation and minimal_automation are True, it will
        only rely upon known evaluations of the operands to determine
        whether to try to prove or disprove the disjunction.
        '''
        from proveit.logic import TRUE, SimplificationError
        # load in truth-table evaluations
        from . import or_t_t, or_t_f, or_f_t, or_f_f
        if self.operands.num_entries() == 0:
            from proveit.logic.booleans.disjunction import \
                empty_disjunction_eval
            # Or() = TRUE     
            return empty_disjunction_eval

        # First just see if it has a known evaluation.
        try:
            return Operation.evaluation(self, automation=False)
        except SimplificationError as e:
            if not defaults.automation:
                raise e

        # Depending upon evaluations of operands, we will either
        # attempt to prove or disprove this conjunction.
        if defaults.minimal_automation:
            # Only do non-automated evaluations of operands
            # if minimal_automation is True.
            operand_automations = (False,)
        else:
            # First try non-automated operand evaluation, then
            # automated only if necessary.
            operand_automations = (False, True)
        for operand_automation in operand_automations:
            operands_evals = []
            for operand in self.operands:
                try:
                    operand_eval = operand.evaluation(
                            automation=operand_automations)
                    operands_evals.append(operand_eval.rhs)
                except BaseException:
                    operands_evals.append(None)
            if TRUE in operands_evals:
                # If any operand is true, the disjunction may
                # only evaluate to true if it can be evaluated.
                self.prove()
                break
            elif None not in operands_evals:
                # If no operand is true and all the evaluations
                # are known, the conjunction may only evaluate
                # to false if it can be evaluated.
                self.disprove()
                break

        # If we had any success proving or disproving this conjunction
        # there should be a known evaluation now.
        return Operation.evaluation(self, automation=False)
    """
    
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Return the "And(a) = a" simplification if applicable,
        or the default reflexive equality otherwise.
        '''
        if self.operands.is_single():
            return self.unary_reduction()

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        if Or._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested disjunctions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                if isinstance(operand, Or):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, auto_simplify=False))
                length = expr.operands.num_entries()
                _n += 1

        return Expression.shallow_simplification(self)

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From (A or B), and assuming not(A) and not(B), 
        derive and return FALSE.
        '''
        from . import binary_or_contradiction, or_contradiction
        if self.operands.is_double():
            return binary_or_contradiction.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        else:
            _A = self.operands
            _m = self.operands.num_elements()
            return or_contradiction.instantiate({m: _m, A: _A}, preserve_all=True) #, preserved_exprs={_A})

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From (A or B), derive the conclusion provided that the negated
        conclusion implies not(A) and not(B), and the conclusion is a
        Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''

        From (A or B), derive the negated conclusion provided that the
        conclusion implies both not(A) and not(B), and the conclusion 
        is a Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion)

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this 'or' expression 
        is in the set of BOOLEANS.
        '''
        from . import binary_closure, closure
        if self.operands.is_double():
            return binary_closure.instantiate(
                {A: self.operands[0], B: self.operands[1]},
                preserve_expr=self)
        else:
            _A = self.operands
            _m = _A.num_elements()
            return closure.instantiate(
                {m: _m, A: _A}, preserve_expr=self)

    @prover
    def conclude_via_example(self, true_operand, **defaults_config):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the set of BOOLEANS.
        '''
        from . import or_if_any, or_if_left, or_if_right
        index = self.operands.index(true_operand)
        if self.operands.is_double():
            if index == 0:
                return or_if_left.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
            elif index == 1:
                return or_if_right.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
        _A, _B, _C = (self.operands[:index], self.operands[index],
                      self.operands[index + 1:])
        _m = _A.num_elements()
        _n = _C.num_elements()
        return or_if_any.instantiate({m: _m, n: _n, A: _A, B: _B, C: _C})

    @prover
    def conclude_via_some(self, subset_disjunction, **defaults_config):
        '''
        From some true (or assumed true) disjunctive subset of the
        operands, conclude that this 'or' expression is true. This is
        similar to the conclude_via_example method above. For example,
        we might have a disjunction such as:
            example_disj = A V B V C V D,
        where we know (or assume) that B V D is true. We could call
            example_disj.conclude_via_some(B V D, assumptions=[B V D]),
        which will return
            {B V D} |– A V B V C V D
        '''
        # Check that the subset_disjunction is an instance of OR
        if not isinstance(subset_disjunction, Or):
            raise TypeError(('subset_disjunction arg should be '
                             'a disjunction (Or)'))
        # Check that each of the operands in subset_disjunction occur as
        # operands in self (otherwise throw a ValueError).
        self_operands = self.operands
        subset_operands = subset_disjunction.operands
        unexpected_operands = list(set(subset_operands) - set(self_operands))
        if len(unexpected_operands) != 0:
            raise ValueError('the disjunctive subset (subset_disjunction) you '
                             'provided contains unexpected items: {}'.
                             format(unexpected_operands))
        # collect the operands not present in the proffered subset
        # (in using set() we are (temporarily) assuming no repeated operands)
        # and let's assume we get a non-empty set
        complementary_operands = list(
            set(self_operands) - set(subset_operands))
        if len(complementary_operands) == 1:
            complementary_disjunction = complementary_operands[0]
        else:
            complementary_disjunction = Or(*complementary_operands)
        # the following produces a permutated, associated version of the
        # original disjunction
        binary_disjunction = (
            Or(subset_disjunction, complementary_disjunction)
            .conclude_via_left()
        )
        # remove the extra parentheses (not yet un-permuting)
        permuted_disjunction = (
            binary_disjunction.disassociate(0).disassociate(-1)
        )

        return self.conclude_via_permutation(permuted_disjunction)

    @prover
    def conclude_via_permutation(self, permuted_disjunction,
                                 **defaults_config):
        '''
        From some true (or assumed true) but permutated version of this
        'or' expression, conclude that this 'or' expression is true.
        For example, let this_or = A V B V C V D
        and let perm_of_this_or = S |- B V A V C V D.
        From perm_of_this_or, conclude this_or, using the following:
        this_or.conclude_via_permuation(perm_of_this_or, assumptions = S),
        which will return S |– A V B V C V D.
        '''

        # Check that the permuted_disjunction is an instance of OR
        # perm_disj_expr = permuted_disjunction.expr
        if not isinstance(permuted_disjunction.expr, Or):
            raise TypeError(('permuted_disjunction arg should be '
                             'a disjunction (Or)'))
        # Check that each of the operands in subset_disjunction occur as
        # operands in self (otherwise throw a ValueError).
        self_operands = self.operands
        perm_operands = permuted_disjunction.operands
        unexpected_operands = list(set(perm_operands) - set(self_operands))
        if len(unexpected_operands) != 0:
            raise ValueError('the permuted disjunction (permuted_disjunction) '
                             'you provided contains unexpected items: {}'.
                             format(unexpected_operands))

        # NOTICE we are assuming no repetition of operands and that
        # len(perm_operands) = self_operands.num_entries()

        for _i in range(self_operands.num_entries()):
            # update the operands list each time for the permuting version
            perm_operands = permuted_disjunction.operands
            temp_operand = self_operands[_i]
            _j = perm_operands.index(temp_operand)
            equiv_permuted_disjunction = (
                permuted_disjunction.commutation(_j, _i)
            )
            permuted_disjunction = (
                equiv_permuted_disjunction
                .sub_right_side_into(permuted_disjunction)
            )

        return permuted_disjunction

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        '''
        For the degenerate case of Or(A), where A is Boolean, derive
        and return |–[V](A) = A. For example, calling
            Or(A).unary_reduction([in_bool(A)])
        will return:
            {A in Bool} |– [V](A) = A
        '''
        from proveit.logic.booleans.disjunction import \
            unary_or_reduction
        if not self.operands.is_single():
            raise ValueError("Or.unary_reduction: expression must have only a "
                             "single operand in order to invoke the "
                             "unary_or_reduction theorem.")
        operand = self.operands[0]
        return unary_or_reduction.instantiate({A: operand})

    @equality_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to 
        a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, (A or B or ... or Y or Z) = (A or ... or Y or B or Z)
        via init_idx = 1 and final_idx = -2.
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
        Or(A,B,C,D).group_commutation(0, 1, length=2,
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

    @prover
    def commute(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        From self, derive and return a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, given (A or B or ... or Y or Z) derive (A or ... or Y or B or Z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commute, leftward_commute, rightward_commute
        return apply_commutation_thm(
            self, init_idx, final_idx, commute,
            leftward_commute, rightward_commute)

    @prover
    def group_commute(self, init_idx, final_idx, length, disassociate=True,
                      **defaults_config):
        '''
        Given self, deduce and return a form in which the operands
        at indices [init_idx, init_idx+length) have been moved to [final_idx. final_idx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return group_commute(
            self, init_idx,  final_idx, length, disassociate)

    @equality_prover('associated', 'associate')  
    def association(self, start_idx, length, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (A or B or ... or Y or Z) = (A or B ... or (L or ... or M) or ... or Y or Z)
        '''
        from . import association
        return apply_association_thm(
            self, start_idx, length, association)

    @prover
    def associate(self, start_idx, length, **defaults_config):
        '''
        From self, derive and return a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, from (A or B or ... or Y or Z) derive
        (A or B ... or (L or ... or M) or ... or Y or Z).
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
            (A or B ... or (L or ... or M) or ... or Y or Z)
        derive (A or B or ... or Y or Z).
        '''
        from . import disassociate
        return apply_disassociation_thm(self, idx, disassociate)

