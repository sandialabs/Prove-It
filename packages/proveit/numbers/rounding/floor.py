from proveit import (defaults, Function, InnerExpr, Literal, USE_DEFAULTS,
                     relation_prover, equality_prover)
from proveit.numbers import NumberOperation
from proveit.numbers.number_sets import Integer, Natural
from proveit.numbers.rounding.rounding_methods import (
    apply_rounding_elimination, apply_rounding_extraction,
    apply_shallow_simplification, rounding_deduce_in_number_set,
    rounding_readily_provable_number_set, rounding_bound_via_operand_bound)


class Floor(NumberOperation, Function):
    # operator of the Floor operation.
    _operator_ = Literal(string_format='floor', theory=__file__)

    def __init__(self, A, *, styles=None):
        Function.__init__(self, Floor._operator_, A, styles=styles)
        # self.operand = A

    def _closureTheorem(self, number_set):
        from . import theorems
        if number_set == Natural:
            return theorems.floor_real_pos_closure
        elif number_set == Integer:
            return theorems.floor_real_closure

    def latex(self, **kwargs):
        return (r'\left\lfloor ' + self.operand.latex(fence=False) 
                + r'\right\rfloor')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Floor
        expression assuming the operands have been simplified.
        
        For the trivial case Floor(x) where the operand x is already
        known to be or assumed to be an integer, derive and return this
        Floor expression equated with the operand itself: Floor(x) = x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification. For the case where the operand is of the
        form x = real + int, derive and return this Floor expression
        equated with Floor(real) + int.
        '''
        return apply_shallow_simplification(self, must_evaluate=must_evaluate)

    @equality_prover('rounding_eliminated', 'rounding_eliminate')
    def rounding_elimination(self, **defaults_config):
        '''
        For the trivial case of Floor(x) where the operand x is already
        an integer, derive and return this Floor expression equated
        with the operand itself: Floor(x) = x. Assumptions may be
        necessary to deduce necessary conditions (for example, that x
        actually is an integer) for the simplification.
        This method is utilized by the do_reduced_simplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be an integer.
        For the case where the operand is of the form x = real + int,
        see the rounding_extraction() method.
        '''
        from . import floor_of_integer

        return apply_rounding_elimination(self, floor_of_integer)

    @equality_prover('rounding_extracted', 'rounding_extract')
    def rounding_extraction(self, idx_to_extract=None, **defaults_config):
        '''
        For the case of Floor(x) where the operand x = x_real + x_int,
        derive and return Floor(x) = Floor(x_real) + int (thus
        'extracting' the integer component out from the Floor() fxn).
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
        from . import floor_of_real_plus_int
        return apply_rounding_extraction(
            self, floor_of_real_plus_int, idx_to_extract)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set, attempt to prove that the given
        Floor expression is in that number set using the appropriate
        closure theorem.
        '''
        from proveit.numbers.rounding import floor_is_an_int
        from proveit.numbers.rounding import floor_real_pos_closure

        return rounding_deduce_in_number_set(
            self, number_set, floor_is_an_int, floor_real_pos_closure)

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        return rounding_readily_provable_number_set(self)

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Deduce a bound on this Ceiling (Ceil) object, given a
        bound (the operand_relation) on its operand.
        '''
        from proveit.numbers.rounding import (
                floor_increasing_less, floor_increasing_less_eq,
                floor_of_real_below_int)

        return rounding_bound_via_operand_bound(
                self, operand_relation, floor_increasing_less,
                floor_increasing_less_eq, floor_of_real_below_int)
