from proveit import (defaults, Function, InnerExpr, Literal, ProofFailure,
                     USE_DEFAULTS, equality_prover)
from proveit.logic import InSet
from proveit.numbers.number_sets import Integer, Natural, Real
from proveit.numbers.rounding.rounding_methods import (
    apply_rounding_elimination, apply_rounding_extraction,
    apply_reduced_simplification, rounding_deduce_in_number_set)


class Round(Function):
    # operator of the Round operation.
    _operator_ = Literal(string_format='round', theory=__file__)

    def __init__(self, A, *, styles=None):
        Function.__init__(self, Round._operator_, A, styles=styles)


    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Returns a proven simplification equation for this Round
        expression assuming the operands have been simplified.
        
        For the trivial case Round(x) where the operand x is already
        known to be or assumed to be an integer, derive and return this
        Round expression equated with the operand itself: Round(x) = x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification. For the case where the operand is of the
        form x = real + int, derive and return this Round expression
        equated with Round(real) + int.
        '''
        return apply_reduced_simplification(self, defaults.assumptions)

    @equality_prover('rounding_eliminated', 'rounding_eliminate')
    def rounding_elimination(self, **defaults_config):
        '''
        For the trivial case of Round(x) where the operand x is already
        an integer, derive and return this Round expression equated
        with the operand itself: Round(x) = x. Assumptions may be
        necessary to deduce necessary conditions (for example, that x
        actually is an integer) for the simplification.
        This method is utilized by the do_reduced_simplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be an integer.
        For the case where the operand is of the form x = real + int,
        see the rounding_extraction() method.
        '''
        from . import round_of_integer
        return apply_rounding_elimination(self, round_of_integer)

    @equality_prover('rounding_extracted', 'rounding_extract')
    def rounding_extraction(self, idx_to_extract=None, **defaults_config):
        '''
        For the case of Round(x) where the operand x = x_real + x_int,
        derive and return Round(x) = Round(x_real) + x_int (thus
        'extracting' the integer component out from the Round() fxn).
        The idx_to_extract is the zero-based index of the item in the
        operands of an Add(a, b, …, n) expression to attempt to extract.
        Assumptions may be necessary to deduce necessary conditions
        (for example, that x_int actually is an integer) for the
        simplification.
        This method is utilized by the do_reduced_simplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be of the form x = x_real + x_int.
        For the case where the entire operand x is itself an integer,
        see the rounding_elimination() method.

        This works only if the operand x is an instance of the Add
        class at its outermost level, e.g. x = Add(a, b, …, n). The
        operands of that Add class can be other things, but the
        extraction is guaranteed to work only if the inner operands
        a, b, etc., are simple.
        '''
        from . import round_of_real_plus_int
        return apply_rounding_extraction(
            self, round_of_real_plus_int, idx_to_extract)

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        Round expression is in that number set using the appropriate
        closure theorem.
        '''
        from proveit.numbers.rounding import round_is_an_int
        from proveit.numbers.rounding import round_real_pos_closure

        return rounding_deduce_in_number_set(
            self, number_set, round_is_an_int, round_real_pos_closure,
            assumptions)
