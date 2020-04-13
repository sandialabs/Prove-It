from proveit import defaults, Function, InnerExpr, Literal, USE_DEFAULTS
from proveit.number.sets import Integers, Naturals, NaturalsPos
from proveit.number.rounding.rounding_methods import apply_roundingElimination

class Ceil(Function):
    # operator of the Ceil operation.
    _operator_ = Literal(stringFormat='ceil', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Ceil._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == NaturalsPos:
            return _theorems_.ceilRealPosClosure
        elif numberSet == Integers:
            return _theorems_.ceilRealClosure

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        Created: 3/30/2020 by wdc.
        Last modified: 3/30/2020 by wdc. Creation. Based on roughly
                       analogous methods in Add and Exp classes. May
                       need to be renamed.

        For the trivial case where the operand is an integer,
        derive and return this Ceil expression equated with the
        operand itself. Assumptions may be necessary to deduce
        necessary conditions for the simplification.
        For the case where the operand is of the form (real + int),
        derive and return this Ceil expression equated with
        Ceil(real) + int.
        CONSIDER ADDING A RECURSIVE COMPONENT to allow further 
        simplfication, for example for Ceil(real + int + int).
        '''
        from proveit._common_ import n, x
        from proveit.number import Add, Integers
        from ._theorems_ import ceilOfInteger, ceilOfRealPlusInt
        try:
            return ceilOfInteger.specialize(
                    {x:self.operand}, assumptions=assumptions)
        except:
            if isinstance(self.operand, Add):
                subops = self.operand.operands
                if len(subops)==2:
                    xsub = subops[0]
                    nsub = subops[1]
                else:
                    xsub = Add(subops[:-1])
                    n: subops[-1]
                return ceilOfRealPlusInt.specialize(
                        {x:xsub, n:nsub}, assumptions=assumptions)
            else:
                raise ValueError("Ceil.doReducedSimplification() method "
                                 "expecting simpler operands. Consider "
                                 "reviewing the ceilOfInteger and "
                                 "ceilOfRealPlusInt theorems in the "
                                 "proveit/number/rounding context.")

    # def roundingElimination(self, assumptions=USE_DEFAULTS):
    #     '''
    #     For the trivial case of Ceil(x) where the operand x is already
    #     an integer, derive and return this Ceil expression equated
    #     with the operand itself: Ceil(x) = x. Assumptions may be
    #     necessary to deduce necessary conditions (for example, that x
    #     actually is an integer) for the simplification.
    #     This method is utilized by the doReducedSimplification() method
    #     only after the operand x is verified to already be proven
    #     (or assumed) to be an integer.
    #     For the case where the operand is of the form x = real + int,
    #     see the roundingExtraction() method.
    #     '''
    #     from proveit._common_ import x
    #     from ._theorems_ import ceilOfInteger

    #     # among other things, convert any assumptions=None
    #     # to assumptions=() to avoid later len() errors
    #     assumptions = defaults.checkedAssumptions(assumptions)

    #     return ceilOfInteger.specialize(
    #                 {x:self.operand}, assumptions=assumptions)

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
        from proveit import TransRelUpdater
        from proveit._common_ import n, x, y
        from proveit.logic import Equals
        from proveit.number import one, two, Add
        from ._theorems_ import ceilOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=() to avoid later len() errors
        assumptions = defaults.checkedAssumptions(assumptions)

        expr = self

        # for convenience while updating our equation
        eq = TransRelUpdater(expr, assumptions)

        # first use Add.commutation to (re-)arrange operands to comform
        # to theorem format, using user-supplied idx_to_extract
        if isinstance(self.operand, Add):
            expr = eq.update(self.innerExpr().operand.commutation(idx_to_extract,
                    len(self.operand.operands)-1, assumptions=assumptions))

            # An association step -- because the later application of
            # the floorOfRealPlusInt thm produces a grouping of the 
            # Floor operands in the chain of equivalences.
            # BUT, only perform the association if multiple operands are
            # needing to be associated:
            if len(expr.operand.operands)-1 > 1:
                expr = eq.update(expr.innerExpr().operand.association(
                        0, len(expr.operand.operands)-1, assumptions=assumptions))


            # then update by applying the floorOfRealPlusInt thm
            x_sub = expr.operand.operands[0]
            n_sub = expr.operand.operands[1]
            expr = eq.update(ceilOfRealPlusInt.specialize(
                    {x:x_sub, n:n_sub}, assumptions=assumptions))

            return eq.relation
        else:
            raise ValueError("In attempting Ceil(x).roundingExtraction(), "
                             "the operand x is not of class 'Add'.")

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        Created: 3/28/2020 by wdc, based on similar methods in Add, Exp,
                 etc., classes.
        Last Modified: 3/28/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        from proveit._common_ import x
        from proveit.logic import InSet
        from proveit.number.rounding._theorems_ import (
                  ceilRealClosure, ceilRealPosClosure)

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integers:
            return ceilRealClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        if number_set == Naturals:
            return ceilRealPosClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        msg = ("'Ceil.deduceInNumberSet()' not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)

# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(
        Ceil, 'roundingElimination', 'roundingEliminated', 'roundingEliminate')
InnerExpr.register_equivalence_method(
        Ceil, 'roundingExtraction', 'roundingExtracted', 'roundingExtract')
