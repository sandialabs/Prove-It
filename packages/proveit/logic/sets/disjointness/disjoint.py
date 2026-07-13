from proveit import (
        n, A, B, S, T, X, Y, equality_prover, Function, Literal, prover)

class Disjoint(Function):
    '''
    The Disjoint operation defines a property for a collection of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of any two of the sets is the empty set.
    We define this property to be True when given zero or one set
    (there are no pairs of sets, so all pairs are vacuously disjoint).
    '''
    _operator_ = Literal('disjoint', r'\textrm{disjoint}', theory=__file__)

    def __init__(self, *sets, styles=None):
        Function.__init__(self, Disjoint._operator_, sets,
                          styles=styles)
        self.sets = self.operands

    def side_effects(self, judgment):
        '''
        Unfold the disjointess claim as a side effect.
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        For self = Disjoint(A,B) (i.e., the binary case), deduce and
        return:
                [Disjoint(A, B) = (Intersect(A,B) = EmptySet)].

        For self = Disjoint(A1, A2, ..., An), deduce and return:

                Disjoint(A1, A2, ..., An) =
                Forall_{X, Y in {A1,...,An} | X ≠ Y} [Disjoint(X, Y)]

        Worth noting that the more general second case will be
        difficult to use when trying to move right-to-left, but can
        still be quite useful moveing left-to-right and using the
        result to then deduce that some (or any) particular pair in
        {A1,...,An} is disjoint.
        '''

        if self.operands.is_double():
            # self has the form Disjoint(A, B)
            from . import disjoint_pair_def_eq
            _A_sub = self.operands[0]
            _B_sub = self.operands[1]
            return disjoint_pair_def_eq.instantiate({A:_A_sub, B:_B_sub})

        if self.operands.num_elements().as_int() > 2:
            # self has the form Disjoint(A1, A2, ..., An)
            from . import nary_disjoint_def
            _n_sub = self.operands.num_elements()
            _A_sub = self.operands
            return nary_disjoint_def.instantiate({n:_n_sub, A:_A_sub})

        else:
            _num_ops = self.operands.num_elements()
            raise NotImplementedError(
                    "Disjoint.definition() only implemented for the "
                    "binary case and cannot yet handle the current case "
                    f"of {self} with {_num_ops} operands. ")

    def as_defined(self, **defaults_config):
        '''
        For self = Disjoint(A,B) (i.e., the binary case), return the
        definitional expression (i.e., NOT a judgment):
        
                (Intersect(A,B) = EmptySet)

        For self = Disjoint(A1, A2, ..., An), return the definitional
        expression (i.e., NOT a judgment):

                Forall_{X, Y in {A1,...,An} | X ≠ Y} [Disjoint(X, Y)]
        '''
        _operands = self.operands
        if _operands.is_double():
            from proveit.logic import Equals
            from proveit.logic.sets import EmptySet, Intersect
            return Equals(Intersect(*_operands), EmptySet)

        if _operands.num_elements().as_int() > 2:
            from proveit import X, Y
            from proveit.logic import NotEquals, Forall
            from proveit.logic.sets import Disjoint, Set
            return Forall((X, Y), Disjoint(X, Y),
                    conditions=[NotEquals(X, Y)],
                    domain=Set(*_operands))

        raise NotImplementedError(
                "Disjoint.definition() only implemented for cases "
                f"with 2 or more operands; the case {self} has "
                "1 or fewer operands.")

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = Disjoint(A, B), and knowing or assuming self,
        derive and return:

                |- Intersect(A, B) = EmptySet

        From self = Disjoint(A1, A2, ..., An), and knowing or assuming
        self, derive and return:

                |- Forall_{X,Y in {A1,...,An}|X≠Y}[Disjoint(X, Y)]
        '''
        if self.operands.is_double():
            # self has the form Disjoint(A, B)
            from . import disjoint_pair_unfolding
            _A_sub = self.operands[0]
            _B_sub = self.operands[1]
            return disjoint_pair_unfolding.instantiate(
                    {A:_A_sub, B:_B_sub})

        # otherwise we try the more general
        if self.operands.num_elements().as_int() > 2:
            # self has the form Disjoint(A1, A2, ..., An)
            from . import nary_disjoint_unfolding
            _n_sub = self.operands.num_elements()
            _A_sub = self.operands
            return nary_disjoint_unfolding.instantiate({n:_n_sub, A:_A_sub})

        raise NotImplementedError(
                "Disjoint.unfold() only implemented for cases "
                f"with 2 or more operands; the case {self} has "
                "1 or fewer operands.")

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude that Disjoint(A1, A2, ..., An) is true (i.e. that
        the sets A1, A2, ..., An are all pairwise disjoint.
        If one of the sets has a 'deduce_disjointness' method, we try
        that (which currently only works for integer Intervals).
        Otherwise, this depends on knowing or assuming that all
        pairwise operand comparisons are disjoint (or in the simple
        binary case Disjoint(A, B), that Intersect(A, B) = EmptySet).
        '''
        for operand in self.sets:
            if hasattr(operand, 'deduce_disjointness'):
                return operand.deduce_disjointness(self)
        if self.operands.is_double():
            # self has the form Disjoint(A, B)
            # We first check for some special cases
            # (1) Disjoint(A-S, B-T)
            # (2) Disjoint(A-S, B)
            # (3) Disjoint(A, B-T)
            from proveit.logic.sets import Difference
            _diff_0 = isinstance(self.operands[0], Difference)
            if _diff_0:
                _A_sub = self.operands[0].operands[0]
                _S_sub = self.operands[0].operands[1]
            else:
                _A_sub = self.operands[0]
            _diff_1 = isinstance(self.operands[1], Difference)
            if _diff_1:
                _B_sub = self.operands[1].operands[0]
                _T_sub = self.operands[1].operands[1]
            else:
                _B_sub = self.operands[1]
            if Disjoint(_A_sub, _B_sub).readily_provable():
                if (_diff_0 and _diff_1):
                    from . import disjoint_imp_disjoint_diffs
                    return (disjoint_imp_disjoint_diffs.instantiate(
                        {A:_A_sub, B:_B_sub, S:_S_sub, T:_T_sub}).
                        derive_consequent())
                elif _diff_0:
                    from . import disjoint_imp_disjoint_diff_left
                    return (disjoint_imp_disjoint_diff_left.instantiate(
                        {A:_A_sub, B:_B_sub, S:_S_sub}).
                        derive_consequent())
                elif _diff_1:
                    from . import disjoint_imp_disjoint_diff_right
                    return (disjoint_imp_disjoint_diff_right.instantiate(
                        {A:_A_sub, B:_B_sub, T:_T_sub}).
                        derive_consequent())

            # We also have a general subset-related case where
            # Disjoint(A,B) => Disjoint(X, Y),
            # if SubsetEq(X,A) and SubsetEq(Y,B). But not clear how to
            # find the supersets A, B that might apply. TBA

            # Then the more general binary case, where we know
            # or assume that the intersection is empty
            from . import disjoint_pair_folding
            _A_sub = self.operands[0]
            _B_sub = self.operands[1]
            return disjoint_pair_folding.instantiate(
                    {A:_A_sub, B:_B_sub})

        # otherwise we try the more general nary case
        if self.operands.num_elements().as_int() > 2:
            # self has the form Disjoint(A1, A2, ..., An)
            from . import nary_disjoint_folding
            _n_sub = self.operands.num_elements()
            _A_sub = self.operands
            return nary_disjoint_folding.instantiate({n:_n_sub, A:_A_sub})

        raise NotImplementedError(
                f"Cannot conclude {self}; non of the sets have a "
                "'deduce_disjointness' method, and it is unknown if the "
                "sets are all pairwise disjoint and unknown if all "
                "pairwise intersections are empty.")

    @prover
    def conclude_via_disjoint_supersets(self, supersets, **defaults_config):
        '''
        Conclude self of the form Disjoint(X, Y) given supersets [A, B]
        such that SubsetEq(X,A) and SubsetEq(Y,B) and Disjoint(A,B).
        That is: we can conclude two sets X, Y are disjoint if we know
        X and Y are respectively subsets of two disjoint sets.
        Currently only implemented for the binary Disjoint(X, Y) case.
        '''
        if (len(self.operands) != 2):
            raise ValueError(
                    "Disjoint.conclude_via_disjoint_supersets() called "
                    f"self = {self}, but "
                    "Disjoint.conclude_via_disjoint_supersets() is "
                    "implemented only for the binary case (i.e. cases ) "
                    "with exactly 2 operands).")

        if not isinstance(supersets, (list, tuple)):
            raise ValueError(
                    "In calling Disjoint.conclude_via_disjoint_supersets() "
                    "the supplied supersets should be a list or tuple "
                    "of exactly two sets.")

        if (len(supersets) != 2):
            raise ValueError(
                    "In calling Disjoint.conclude_via_disjoint_supersets() "
                    "the supplied supersets should be a list or tuple "
                    "of exactly two sets.")

        from . import disjoint_imp_disjoint_subsets
        _A_sub = supersets[0]
        _B_sub = supersets[1]
        _X_sub = self.operands[0]
        _Y_sub = self.operands[1]
        return (disjoint_imp_disjoint_subsets.instantiate(
                {A:_A_sub, B:_B_sub, X:_X_sub, Y:_Y_sub}).
                derive_consequent())



class AllDisjoint(Function):
    '''
    AllDisjoint(S) represents the claim that all sets within a
    collection S of sets are disjoint. The "collection" of sets
    could be a tuple of sets (translated in Prove-It into an ExprTuple
    of sets) or a Prove-It Set of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of every pair of the sets is the empty
    set. We define this property to be True when given zero or one set
    (there are no pairs of sets, so all distinct pairs are vacuously
    disjoint).
    '''
    _operator_ = Literal('AllDisjoint', r'\textrm{AllDisjoint}',
                         theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Initialize the claim that the contents of S are all
        disjoint: AllDisjoint(S)
        '''

        super().__init__(AllDisjoint._operator_, S, styles=styles)
        self.collection = S

    def _function_formatted(self, format_type, **kwargs):
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        formatted_operator = self.operator.formatted(format_type, fence=True)
        lparen = r'\left(' if format_type=='latex' else '('
        rparen = r'\right)' if format_type=='latex' else ')'
        if (hasattr(self, 'operand') and 
                not isinstance(self.operand, ExprTuple)):
            formatted_operand = self.operand.formatted(
                    format_type, fence=True) # prev False
        else:
            formatted_operand = self.operands.formatted(
                    format_type, fence=True, sub_fence=False) # prev both False

        return (formatted_operator + lparen + formatted_operand + rparen)
