from proveit import (defaults, Function, InnerExpr, Literal,
                     USE_DEFAULTS,
                     relation_prover, equality_prover)
from proveit.numbers import NumberOperation
from proveit.numbers.number_sets import Integer, Natural, NaturalPos
from proveit.numbers.rounding.rounding_methods import (
    apply_rounding_elimination, apply_rounding_extraction,
    apply_shallow_simplification, rounding_deduce_in_number_set,
    rounding_deduce_number_set)


class Ceil(NumberOperation, Function):
    # operator of the Ceil operation.
    _operator_ = Literal(string_format='ceil', theory=__file__)

    def __init__(self, A, *, styles=None):
        Function.__init__(self, Ceil._operator_, A, styles=styles)

    def latex(self, **kwargs):
        return (r'\left\lceil ' + self.operand.latex(fence=False) 
                + r'\right\rceil')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Ceil
        expression assuming the operands have been simplified.
        
        For the trivial case Ceil(x) where the operand x is already
        known to be or assumed to be an integer, derive and return this
        Ceil expression equated with the operand itself: Ceil(x) = x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification. For the case where the operand is of the
        form x = real + int, derive and return this Ceil expression
        equated with Ceil(real) + int.
        '''
        return apply_shallow_simplification(self, must_evaluate=must_evaluate)

    @equality_prover('rounding_eliminated', 'rounding_eliminate')
    def rounding_elimination(self, **defaults_config):
        '''
        For the trivial case of Ceil(x) where the operand x is already
        an integer, derive and return this Ceil expression equated
        with the operand itself: Ceil(x) = x. Assumptions may be
        necessary to deduce necessary conditions (for example, that x
        actually is an integer) for the simplification.
        This method is utilized by the do_reduced_simplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be an integer.
        For the case where the operand is of the form x = real + int,
        see the rounding_extraction() method.
        '''
        from . import ceil_of_integer

        return apply_rounding_elimination(self, ceil_of_integer)

    @equality_prover('rounding_extracted', 'rounding_extract')
    def rounding_extraction(self, idx_to_extract=None, **defaults_config):
        '''
        For the case of Ceil(x) where the operand x = x_real + x_int,
        derive and return Ceil(x) = Ceil(x_real) + int (thus
        'extracting' the integer component out from the Ceil() fxn).
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
        from . import ceil_of_real_plus_int
        return apply_rounding_extraction(
            self, ceil_of_real_plus_int, idx_to_extract)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set, attempt to prove that the given
        Ceil expression is in that number set using the appropriate
        closure theorem.
        '''
        from proveit.numbers.rounding import ceil_is_an_int
        from proveit.numbers.rounding import ceil_real_pos_closure

        return rounding_deduce_in_number_set(
            self, number_set, ceil_is_an_int, ceil_real_pos_closure)

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most 
        restrictive standard number set we can readily know.
        '''
        return rounding_deduce_number_set(self)
