from proveit import (defaults, Function, InnerExpr, Literal, ProofFailure,
                     USE_DEFAULTS)
from proveit.logic import InSet
from proveit.number.sets import Integers, Naturals, Reals
from proveit.number.rounding.rounding_methods import (
        apply_roundingElimination, apply_roundingExtraction,
        apply_reducedSimplification)

class Round(Function):
    # operator of the Round operation.
    _operator_ = Literal(stringFormat='round', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Round._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case Round(x) where the operand x is already
        known to be or assumed to be an integer, derive and return this
        Round expression equated with the operand itself: Round(x) = x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification. For the case where the operand is of the
        form x = real + int, derive and return this Round expression
        equated with Round(real) + int.
        '''
        # from proveit._common_ import n, x
        # from proveit.logic import InSet
        # from proveit.number import Add, Integers
        # from ._theorems_ import roundOfInteger, roundOfRealPlusInt

        return apply_reducedSimplification(self, assumptions)

    def roundingElimination(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case of Round(x) where the operand x is already
        an integer, derive and return this Round expression equated
        with the operand itself: Round(x) = x. Assumptions may be
        necessary to deduce necessary conditions (for example, that x
        actually is an integer) for the simplification.
        This method is utilized by the doReducedSimplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be an integer.
        For the case where the operand is of the form x = real + int,
        see the roundingExtraction() method.
        '''
        from proveit._common_ import x
        from ._theorems_ import roundOfInteger

        return apply_roundingElimination(self, roundOfInteger, assumptions)

    # def roundingExtraction(self, idx_to_extract=None, assumptions=USE_DEFAULTS):
    #     '''
    #     For the case of Round(x) where the operand x = x_real + x_int,
    #     derive and return Round(x) = Round(x_real) + int (thus
    #     'extracting' the integer component out from the Round() fxn).
    #     The idx_to_extract is the zero-based index of the item in the
    #     operands of an Add(a, b, …, n) expression to attempt to extract.
    #     Assumptions may be necessary to deduce necessary conditions
    #     (for example, that x_int actually is an integer) for the
    #     simplification.
    #     This method is utilized by the doReducedSimplification() method
    #     only after the operand x is verified to already be proven
    #     (or assumed) to be of the form x = x_real + x_int.
    #     For the case where the entire operand x is itself an integer,
    #     see the roundingElimination() method.

    #     This works only if the operand x is an instance of the Add
    #     class at its outermost level, e.g. x = Add(a, b, …, n). The
    #     operands of that Add class can be other things, but the
    #     extraction is guaranteed to work only if the inner operands
    #     a, b, etc., are simple.
    #     '''
    #     from proveit import TransRelUpdater
    #     from proveit._common_ import n, x, y
    #     from proveit.logic import Equals
    #     from proveit.number import one, two, Add
    #     from ._theorems_ import roundOfRealPlusInt

    #     # among other things, convert any assumptions=None
    #     # to assumptions=() to avoid later len() errors
    #     assumptions = defaults.checkedAssumptions(assumptions)

    #     expr = self

    #     # for convenience while updating our equation
    #     eq = TransRelUpdater(expr, assumptions)

    #     # first use Add.commutation to (re-)arrange operands to comform
    #     # to theorem format, using user-supplied idx_to_extract
    #     if isinstance(self.operand, Add):
    #         expr = eq.update(self.innerExpr().operand.commutation(idx_to_extract,
    #                 len(self.operand.operands)-1, assumptions=assumptions))

    #         # An association step -- because the later application of
    #         # the roundOfRealPlusInt thm produces a grouping of the 
    #         # Round operands in the chain of equivalences.
    #         # BUT, only perform the association if multiple operands are
    #         # needing to be associated:
    #         if len(expr.operand.operands)-1 > 1:
    #             expr = eq.update(expr.innerExpr().operand.association(
    #                     0, len(expr.operand.operands)-1, assumptions=assumptions))


    #         # then update by applying the roundOfRealPlusInt thm
    #         x_sub = expr.operand.operands[0]
    #         n_sub = expr.operand.operands[1]
    #         expr = eq.update(roundOfRealPlusInt.specialize(
    #                 {x:x_sub, n:n_sub}, assumptions=assumptions))

    #         return eq.relation
    #     else:
    #         raise ValueError("In attempting Round(x).roundingExtraction(), "
    #                          "the operand x is not of class 'Add'.")

    def roundingExtraction(self, idx_to_extract=None, assumptions=USE_DEFAULTS):
        '''
        For the case of Round(x) where the operand x = x_real + x_int,
        derive and return Round(x) = Round(x_real) + int (thus
        'extracting' the integer component out from the Round() fxn).
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
        from ._theorems_ import roundOfRealPlusInt
        return apply_roundingExtraction(
                self, roundOfRealPlusInt, idx_to_extract, assumptions)

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        Round expression is in that number set using the appropriate
        closure theorem.
        '''
        from proveit._common_ import x
        from proveit.logic import InSet
        from proveit.number.rounding._theorems_ import (
                  roundRealClosure, roundRealPosClosure)

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integers:
            return roundRealClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        if number_set == Naturals:
            return roundRealPosClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        msg = ("'Round.deduceInNumberSet()' not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)


# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(
        Round, 'roundingElimination', 'roundingEliminated', 'roundingEliminate')
InnerExpr.register_equivalence_method(
        Round, 'roundingExtraction', 'roundingExtracted', 'roundingExtract')
            
