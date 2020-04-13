from proveit import (defaults, Function, InnerExpr, Literal, ProofFailure,
                     USE_DEFAULTS)
from proveit.logic import InSet
from proveit.number.sets import Integers, Naturals, Reals

class Round(Function):
    # operator of the Round operation.
    _operator_ = Literal(stringFormat='round', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Round._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == Naturals:
            return _theorems_.roundRealPosClosure
        elif numberSet == Integers:
            return _theorems_.roundRealClosure

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
        from proveit._common_ import n, x
        from proveit.logic import InSet
        from proveit.number import Add, Integers
        from ._theorems_ import roundOfInteger, roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        #-- Case (1): Round(x)                                       --#
        #-- Entire operand x is known or assumed to be an Integer.   --#
        if InSet(self.operand, Integers).proven(assumptions=assumptions):
            # Entire operand is known to be or assumed to be an integer
            # so we can simply remove the Round() wrapper
            return self.roundingElimination(assumptions)
        #-- Case (2): Round(x) = Round(Add(a,b,...,n))               --#
        #-- Operand x is an Add object, not known or assumed to be   --#
        #-- an int, but addends might be reals and ints              --#
        elif isinstance(self.operand, Add):
            # Try to partition all suboperands into ints vs. reals
            from proveit import TransRelUpdater
            tempExpr = self
            # for convenience while updating our equation
            eq = TransRelUpdater(tempExpr, assumptions)

            subops = self.operand.operands

            # Collect indices of operands known or assumed to be
            # ints versus reals versus neither
            indices_of_known_ints = []
            indices_of_reals_not_ints = []
            indices_of_unknowns = []
            for i in range(len(subops)):
                if InSet(subops[i], Integers).proven(assumptions):
                    indices_of_known_ints.append(i)
                elif InSet(subops[i], Reals).proven(assumptions):
                    indices_of_reals_not_ints.append(i)
                else:
                    indices_of_unknowns.append(i)
            if len(indices_of_unknowns) == 0:
                # each addend is an int or a real, so we should be able
                # to rearrange and partition the addends as such
                original_addends = list(subops)
                desired_order_by_index = list(
                        indices_of_reals_not_ints+indices_of_known_ints)
                # commute to put reals first, followed by ints
                for i in range(len(original_addends)):
                    init_idx = tempExpr.operand.operands.index(
                            original_addends[desired_order_by_index[i]])
                    tempExpr = eq.update(self.innerExpr().operand.commutation(
                        init_idx, i, assumptions=assumptions))

                # associate the reals
                if len(indices_of_reals_not_ints) > 1:
                    # associate those elements (already re-arranged to
                    # be at the front of the operand.operands):
                    tempExpr = eq.update(
                            tempExpr.innerExpr().operand.association(
                                    0, len(indices_of_reals_not_ints),
                                    assumptions=assumptions))
                # associate the ints
                if len(indices_of_known_ints) > 1:
                    # associate those elements (already re-arranged to
                    # be at the end of the operand.operands):
                    tempExpr = eq.update(
                            tempExpr.innerExpr().operand.association(
                                    1, len(indices_of_known_ints),
                                    assumptions=assumptions))

                tempExpr = eq.update(tempExpr.roundingExtraction(1, assumptions))
                return eq.relation

            else:
                list_of_unknowns = [subops[i] for i in indices_of_unknowns]
                msg = ("In Round.doReducedSimplification, operands {} not "
                       "assumed or proven to be Integers or Reals.".
                       format(list_of_unknowns))
                raise ValueError(msg)
        else:
            raise ValueError("Round.doReducedSimplification() method "
                             "expecting simpler operands. Consider "
                             "reviewing the roundOfInteger and "
                             "roundOfRealPlusInt theorems in the "
                             "proveit/number/rounding context.")

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

        # among other things, convert any assumptions=None
        # to assumptions=() to avoid later len() errors
        assumptions = defaults.checkedAssumptions(assumptions)

        return roundOfInteger.specialize(
                    {x:self.operand}, assumptions=assumptions)

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
        from proveit import TransRelUpdater
        from proveit._common_ import n, x, y
        from proveit.logic import Equals
        from proveit.number import one, two, Add
        from ._theorems_ import roundOfRealPlusInt

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
            # the roundOfRealPlusInt thm produces a grouping of the 
            # Round operands in the chain of equivalences.
            # BUT, only perform the association if multiple operands are
            # needing to be associated:
            if len(expr.operand.operands)-1 > 1:
                expr = eq.update(expr.innerExpr().operand.association(
                        0, len(expr.operand.operands)-1, assumptions=assumptions))


            # then update by applying the roundOfRealPlusInt thm
            x_sub = expr.operand.operands[0]
            n_sub = expr.operand.operands[1]
            expr = eq.update(roundOfRealPlusInt.specialize(
                    {x:x_sub, n:n_sub}, assumptions=assumptions))

            return eq.relation
        else:
            raise ValueError("In attempting Round(x).roundingExtraction(), "
                             "the operand x is not of class 'Add'.")

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
            
