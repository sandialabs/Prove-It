from proveit import (Literal, Operation, defaults, USE_DEFAULTS, 
                     ProofFailure, prover, relation_prover, equality_prover)
from proveit.logic.booleans.conjunction import compose
from .implies import Implies
from proveit import A, B, C
from proveit import TransitiveRelation

# if and only if: A => B and B => A


class Iff(TransitiveRelation):
    # The operator of the Iff operation
    _operator_ = Literal(
        string_format='<=>',
        latex_format=r'\Leftrightarrow',
        theory=__file__)

    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, A, B, *, styles=None):
        TransitiveRelation.__init__(self, Iff._operator_, A, B,
                                    styles=styles)
        self.A = A
        self.B = B

    def side_effects(self, judgment):
        '''
        Yield the TransitiveRelation side-effects (which also records known_left_sides
        and known_right_sides).  Also derive the left and right implications,
        derive the reversed version and attempt to derive equality.
        '''
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        yield self.derive_left_implication  # B=>A given A<=>B
        yield self.derive_right_implication  # A=>B given A<=>B
        yield self.derive_reversed  # B<=>A given A<=>B
        # A=B given A<=>B (assuming A and B are in booleans)
        yield self.derive_equality

    def _readily_provable(self):
        '''
        A <=> B is readily provable if A => B and B => A are rediable
        provable or if A and B are both readily provable or both 
        readily disprovable.
        '''
        return ((Implies(self.A, self.B).readily_provable() and
                Implies(self.B, self.A).readily_provable()) or
            (self.A.readily_provable() and self.B.readily_provable()) or (
            self.A.readily_disprovable() and (self.B.readily_disprovable())))

    def _readily_disprovable(self):
        '''
        A <=> B is readily provable if A => B is readily disprovable or
        B => A is readily disprovable or if A is readily provable and 
        B is readily disprovable or vice-versa.
        '''
        return (Implies(self.A, self.B).readily_disprovable() or
                Implies(self.B, self.A).readily_disprovable() or 
                (self.antecedent.readily_disprovable() and 
                 self.consequent.readily_provable()) or
                 (self.antecedent.readily_provable() and (
                    self.consequent.readily_disprovable())))

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to automatically conclude this Iff given both operands
        are true, both operands are false, or by proving implications
        in both direction (the definition).
        '''
        from . import iff_t_t, iff_t_f, iff_f_t, iff_f_f, true_iff_true, false_iff_false
        if self in {true_iff_true, false_iff_false}:
            # should be proven via one of the imported theorems as a 
            # simple special case
            try:
                self.shallow_simplification()
                # self.evaluation()
            except BaseException:
                return self.prove()
        if self.A.readily_provable() and self.B.readily_provable():
            # A <=> B because A and B are both true.
            from . import iff_via_both_true
            return iff_via_both_true.instantiate({A:self.A, B:self.B})
        if  self.A.readily_disprovable() and self.B.readily_disprovable():
            # A <=> B because A and B are both false.
            from . import iff_via_both_false
            return iff_via_both_false.instantiate({A:self.A, B:self.B})
        # Introduce the Iff via implications each way as a direct 
        # consequence of the definition.
        return self.conclude_by_definition()

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Try to automatically conclude the negation of Iff given one
        operand is true and the other is false or by proving 
        the implication in one of the directions is False.
        '''
        from proveit.logic.booleans import FALSE, TRUE
        if self.A == TRUE and self.B == FALSE:
            from . import true_iff_false_negated
            return true_iff_false_negated
        elif self.B == TRUE and self.A == FALSE:
            from . import false_iff_true_negated
            return false_iff_true_negated
        elif self.A.readily_provable() and self.B.readily_disprovable():
            from . import not_iff_via_not_right
            return not_iff_via_not_right.instantiate({A:self.A, B:self.B})
        elif self.A.readily_disprovable() and self.B.readily_provable():
            from . import not_iff_via_not_left
            return not_iff_via_not_left.instantiate({A:self.A, B:self.B})
        elif Implies(self.A, self.B).readily_disprovable():
            from . import not_iff_via_not_right_impl
            return not_iff_via_not_right_impl.instantiate({A:self.A, B:self.B})
        elif Implies(self.B, self.A).readily_disprovable():
            from . import not_iff_via_not_left_impl
            return not_iff_via_not_left_impl.instantiate({A:self.A, B:self.B})
        raise ProofFailure(self, defaults.assumptions,
                           "Unable to automatically conclude by "
                           "standard means.")
    @prover
    def derive_left_implication(self, **defaults_config):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        from . import iff_implies_left
        return iff_implies_left.instantiate(
            {A: self.A, B: self.B})

    @prover
    def derive_left(self, **defaults_config):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        from . import left_from_iff
        return left_from_iff.instantiate(
            {A: self.A, B: self.B})

    @prover
    def derive_right_implication(self, **defaults_config):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        from . import iff_implies_right
        return iff_implies_right.instantiate(
            {A: self.A, B: self.B})

    @prover
    def derive_right(self, **defaults_config):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        from . import right_from_iff
        return right_from_iff.instantiate(
            {A: self.A, B: self.B})

    @prover
    def derive_reversed(self, **defaults_config):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        from . import iff_symmetry
        return iff_symmetry.instantiate(
            {A: self.A, B: self.B})

    @prover
    def apply_transitivity(self, other_iff, **defaults_config):
        '''
        From A <=> B (self) and the given B <=> C (other_iff) derive and return
        (A <=> C) assuming self and other_iff.
        Also works more generally as long as there is a common side to the equations.
        '''
        from . import iff_transitivity
        assert isinstance(other_iff, Iff)
        if self.B == other_iff.A:
            # from A <=> B, B <=> C, derive A <=> C
            return iff_transitivity.instantiate(
                {A: self.A, B: self.B, C: other_iff.B},
                preserve_all=True)
        elif self.A == other_iff.A:
            # from y = x and y = z, derive x = z
            return self.derive_reversed().apply_transitivity(other_iff)
        elif self.A == other_iff.B:
            # from y = x and z = y, derive x = z
            return self.derive_reversed().apply_transitivity(
                other_iff.derive_reversed())
        elif self.B == other_iff.B:
            # from x = y and z = y, derive x = z
            return self.apply_transitivity(
                other_iff.derive_reversed())
        else:
            assert False, ('transitivity cannot be applied unless there '
                           'is something in common in the equalities')

    @equality_prover("defined", "define")
    def definition(self, **defaults_config):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        from . import iff_def
        return iff_def.instantiate({A: self.A, B: self.B})

    @prover
    def conclude_by_definition(self, **defaults_config):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        from . import iff_intro
        return iff_intro.instantiate({A: self.A, B: self.B})

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        If the operands that to TRUE or FALSE, we can 
        evaluate this expression as TRUE or FALSE.
        '''
        from proveit.logic import TRUE, FALSE
        # Load in truth-table evaluations
        from . import iff_t_t, iff_t_f, iff_f_t, iff_f_f
        if must_evaluate:
            start_over = False
            for operand in self.operands:
                if operand not in (TRUE, FALSE):
                    # The simplification of the operands may not have
                    # worked hard enough.  Let's work harder if we
                    # must evaluate.
                    operand.evaluation()
                    start_over = True
            if start_over: return self.evaluation()
        # May now be able to evaluate via loaded truth tables.
        return Operation.shallow_simplification(
                self, must_evaluate=must_evaluate)

    def readily_in_bool(self):
        '''
        Returns True if we can readily prove that the operands are
        provably boolean and therefore this Iff is boolean.
        '''
        from proveit.logic import in_bool
        return (in_bool(self.antecedent).readily_provable() and
                in_bool(self.consequent).readily_provable())

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        from . import iff_closure
        return iff_closure.instantiate(
            {A: self.A, B: self.B})

    @prover
    def derive_equality(self, **defaults_config):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        from . import eq_from_iff, eq_from_mutual_impl
        # We must be able to prove this Iff to do this derivation --
        # then either eq_from_iff or eq_from_mutual_impl can be used.
        self.prove()
        # eq_from_mutual_impl may make for a shorter proof; do it both ways (if
        # both are usable)
        if not eq_from_iff.is_usable():
            return eq_from_mutual_impl.instantiate(
                {A: self.A, B: self.B})
        eq_from_mutual_impl.instantiate(
            {A: self.A, B: self.B})
        return eq_from_iff.instantiate(
            {A: self.A, B: self.B})
