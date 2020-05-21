from proveit import defaults, Function, InnerExpr, Literal, USE_DEFAULTS
from proveit.number.sets import Integers, Naturals, NaturalsPos
from proveit.number.rounding.rounding_methods import (
    apply_roundingElimination, apply_roundingExtraction,
    apply_reducedSimplification, rounding_deduceInNumberSet)

class Ceil(Function):
    # operator of the Ceil operation.
    _operator_ = Literal(stringFormat='ceil', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Ceil._operator_, A)

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case Ceil(x) where the operand x is already
        known to be or assumed to be an integer, derive and return this
        Ceil expression equated with the operand itself: Ceil(x) = x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification. For the case where the operand is of the
        form x = real + int, derive and return this Ceil expression
        equated with Ceil(real) + int.
        '''
        return apply_reducedSimplification(self, assumptions)

    def roundingElimination(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case of Ceil(x) where the operand x is already
        an integer, derive and return this Ceil expression equated
        with the operand itself: Ceil(x) = x. Assumptions may be
        necessary to deduce necessary conditions (for example, that x
        actually is an integer) for the simplification.
        This method is utilized by the doReducedSimplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be an integer.
        For the case where the operand is of the form x = real + int,
        see the roundingExtraction() method.
        '''
        from ._theorems_ import ceilOfInteger

        return apply_roundingElimination(self, ceilOfInteger, assumptions)

    def roundingExtraction(self, idx_to_extract=None, assumptions=USE_DEFAULTS):
        '''
        For the case of Ceil(x) where the operand x = x_real + x_int,
        derive and return Ceil(x) = Ceil(x_real) + int (thus
        'extracting' the integer component out from the Ceil() fxn).
        The idx_to_extract is the zero-based index of the item in the
        operands of an Add(a, b, …, n) expression to attempt to extract.
        Assumptions may be necessary to deduce necessary conditions
        (for example, that x_int actually is an integer) for the
        simplification.
        This method is utilized by the doReducedSimplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be of the form x = x_real + x_int.
        For the case where the entire operand x is itself an integer,
        see the roundingElimination() method.

        This works only if the operand x is an instance of the Add
        class at its outermost level, e.g. x = Add(a, b, …, n). The
        operands of that Add class can be other things, but the
        extraction is guaranteed to work only if the inner operands
        a, b, etc., are simple.
        '''
        from ._theorems_ import ceilOfRealPlusInt
        return apply_roundingExtraction(
            self, ceilOfRealPlusInt, idx_to_extract, assumptions)

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        Ceil expression is in that number set using the appropriate
        closure theorem.
        '''
        from proveit.number.rounding._axioms_ import ceilIsAnInt
        from proveit.number.rounding._theorems_ import ceilRealPosClosure

        return rounding_deduceInNumberSet(
            self, number_set, ceilIsAnInt, ceilRealPosClosure,
            assumptions)

# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(
        Ceil, 'roundingElimination', 'roundingEliminated', 'roundingEliminate')
InnerExpr.register_equivalence_method(
        Ceil, 'roundingExtraction', 'roundingExtracted', 'roundingExtract')
