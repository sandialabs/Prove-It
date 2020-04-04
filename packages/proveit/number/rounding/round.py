from proveit import (defaults, Function, InnerExpr, Literal, ProofFailure,
                     USE_DEFAULTS)
from proveit.number.sets import Integers, Naturals

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
        CONSIDER ADDING A RECURSIVE COMPONENT to allow further 
        simplfication, for example for Round(real + int + int).
        '''
        from proveit._common_ import n, x
        from proveit.logic import InSet
        from proveit.number import Add, Integers
        from ._theorems_ import roundOfInteger, roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        # try:
        #     return roundOfInteger.specialize(
        #             {x:self.operand}, assumptions=assumptions)
        # except:
        #     if isinstance(self.operand, Add):
        #         subops = self.operand.operands
        #         if len(subops)==2:
        #             xsub = subops[0]
        #             nsub = subops[1]
        #         else:
        #             xsub = Add(subops[:-1])
        #             nsub: subops[-1]
        #         return roundOfRealPlusInt.specialize(
        #                 {x:xsub, n:nsub}, assumptions=assumptions)
        #     else:
        #         raise ValueError("Round.doReducedSimplification() method "
        #                          "expecting simpler operands. Consider "
        #                          "reviewing the roundOfInteger and "
        #                          "roundOfRealPlusInt theorems in the "
        #                          "proveit/number/rounding context.")
        if InSet(self.operand, Integers).proven(assumptions=assumptions):
            print("entering if branch (operand in Integers)")                   # for testing; delete later
            return self.roundingElimination(assumptions)
            # return roundOfInteger.specialize(
            #         {x:self.operand}, assumptions=assumptions)
        elif isinstance(self.operand, Add):
            print("entering the elif")                                          # for testing; delete later
            subops = self.operand.operands
            print("    subops = {}".format(subops))                             # for testing; delete later
            if len(subops)==2:
                xsub = subops[0]
                nsub = subops[1]
            else:
                xsub = Add(subops[:-1])
                nsub: subops[-1]
            if InSet(nsub, Integers).proven(assumptions=assumptions):
                return roundOfRealPlusInt.specialize(
                        {x:xsub, n:nsub}, assumptions=assumptions)
            else:
                msg = ("{} not yet proven to be in set of Integers.".
                       format(nsub))
                raise ProofFailure(InSet(nsub, Integers), assumptions, msg)
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
        print("Entering roundingElimination() method.")                         # for testing; delete later
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
        '''
        print("Entering roundingExtraction() method.")                          # for testing; delete later
        from proveit import TransRelUpdater
        from proveit._common_ import x
        from proveit.number import Add
        from ._theorems_ import roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=() to avoid later len() errors
        assumptions = defaults.checkedAssumptions(assumptions)

        # for convenience while updating our equation
        eq = TransRelUpdater(self.operand, assumptions)
        print("    eq.relation = {}".format(eq.relation))                       # for testing; delete later

        # first (re-)arrange operands to comform to thm format
        # using user-supplied indx_to_extract
        # use Add.commutation
        if isinstance(self.operand, Add):
            print("Operand is of class 'Add'")                                  # for testing; delete later
            print("    item to extract is: {}".                                 # for testing; delete later
                  format(self.operand.operands[idx_to_extract]))                # for testing; delete later
            expr = eq.update(self.operand.commutation(idx_to_extract,
                    len(self.operand.operands)-1, assumptions=assumptions))
            # eq = self.operand.commutation(
            #     idx_to_extract, len(self.operand.operands)-1,
            #     assumptions=assumptions)
            print("    eq = {}".format(eq))                                     # for testing; delete later
            print("    expr = {}".format(expr))                                 # for testing; delete later
            return eq.relation
        else:
            raise ValueError("Round operand not of class 'Add'.")

        # then apply thm
        # return roundOfInteger.specialize(
        #             {x:self.operand}, assumptions=assumptions)


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
InnerExpr.register_equivalence_method(Round, 'roundingElimination',
                                      'roundingEliminated', 'roundingEliminate')
            
