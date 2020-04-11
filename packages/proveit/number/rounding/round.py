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
            # entire operand is known to be an integer
            return self.roundingElimination(assumptions)
        elif isinstance(self.operand, Add):
            # We have Round(a+b+...+n) but the sum a+b+...+n is not
            # known to be an integer. We can try to:
            # (1) partition the sum into a single integer term plus a
            # sum of (n-1) terms that is known to be real and apply the
            # extraction method; then,
            # (2) repeat the process on the resulting extracted expr.
            print("entering the elif")                                          # for testing; delete later
            subops = self.operand.operands
            print("    subops = {}".format(subops))                             # for testing; delete later
            if len(subops)>2:
                print(" subops rearranged = {} {}".
                      format(subops[1], subops[0:1] + subops[1+1:]))            # for testing; delete later

            for i in range(len(subops)):
                print("testing {} in Integers ...".format(subops[i]))           # for testing; delete later
                print("testing {} in Reals ...".format(subops[0:i]+subops[i+1:])) # for testing; delete later
                if (InSet(subops[i], Integers).proven(assumptions=assumptions) and
                    _allProvenReals(subops[0:i]+subops[i+1:], assumptions=assumptions)):
                    print("{} is an int, all others are real".format(subops[i])) # for testing; delete later
                    return self.roundingExtraction(i, assumptions)
            nsub=''
            if len(subops)==2:
                xsub = subops[0]
                nsub = subops[1]
            else:
                print("len(subops) != 2")
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

        This works only if x is an instance of the Add class at its
        outermost level, e.g. x = Add(a, b, …, n). The operands of that
        Add class can be other things, but the extraction is guaranteed
        to work only if the inner operands a, b, etc., are simple.
        '''
        print("Entering roundingExtraction() method.")                          # for testing; delete later
        from proveit import TransRelUpdater
        from proveit._common_ import n, x, y
        from proveit.logic import Equals
        from proveit.number import one, two, Add
        from ._theorems_ import roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=() to avoid later len() errors
        assumptions = defaults.checkedAssumptions(assumptions)

        expr = self
        print("    expr = {}".format(expr))                                      # for testing; delete later
        print("    expr.innerExpr() = {}".format(expr.innerExpr()))              # for testing; delete later
        print("    expr.innerExpr().operand = {}".format(expr.innerExpr().operand)) # for testing; delete later

        # for convenience while updating our equation
        eq = TransRelUpdater(expr, assumptions)
        print("    eq.relation = {}".format(eq.relation))                       # for testing; delete later

        # first (re-)arrange operands to comform to thm format
        # using user-supplied indx_to_extract
        # use Add.commutation
        if isinstance(self.operand, Add):
            print("    Operand is of class 'Add'")                              # for testing; delete later
            print("    item to extract is {0} and index {1}".                   # for testing; delete later
                  format(self.operand.operands[idx_to_extract], idx_to_extract)) # for testing; delete later
            print("    self.innerExpr().operand = {}".format(self.innerExpr().operand)) # for testing; delete later
            print("    expr.innerExpr().operand = {}".format(expr.innerExpr().operand)) # for testing; delete later
            expr = eq.update(self.innerExpr().operand.commutation(idx_to_extract,
                    len(self.operand.operands)-1, assumptions=assumptions))
            print("After COMMUTATION eq.update():")                             # for testing; delete later
            print("    expr = {}".format(expr))                                 # for testing; delete later
            print("    expr.operand = {}".format(expr.operand))                 # for testing; delete later
            print("    expr.operand.operands = {}".format(expr.operand.operands)) # for testing; delete later
            print("    eq.relation = {}".format(eq.relation))                   # for testing; delete later
            print("    eq.relation.rhs = {}".format(eq.relation.rhs))           # for testing; delete later
            # print("    eq.relation.rhs.exprInfo() = {}".format(eq.relation.rhs.exprInfo()))           # for testing; delete later

            # An association step -- because the later application of
            # the roundOfRealPlusInt thm produces a grouping of the 
            # Round operands in the chain of equivalences. (Actually
            # kind of annoying, because the grouping doesn't appear in
            # the pirnted outputs of the intermediate stages and is thus
            # difficult to catch)
            # BUT, only perform the association multiple operands are
            # needing to be associated:
            if len(expr.operand.operands)-1 > 1:
                expr = eq.update(expr.innerExpr().operand.association(
                        0, len(expr.operand.operands)-1, assumptions=assumptions))

            print("AFTER ASSOCIATION eq.update():")                             # for testing; delete later
            print("    expr = {}".format(expr))                                 # for testing; delete later
            print("    expr.operand = {}".format(expr.operand))                 # for testing; delete later
            print("    expr.operand.operands = {}".format(expr.operand.operands)) # for testing; delete later
            print("    expr.operand.operands[0] = {}".format(expr.operand.operands[0])) # for testing; delete later
            print("    eq.relation = {}".format(eq.relation))                   # for testing; delete later
            print("    eq.relation.rhs = {}".format(eq.relation.rhs))           # for testing; delete later


            # then update by applying the roundOfRealPlusInt thm
            x_sub = expr.operand.operands[0]
            n_sub = expr.operand.operands[1]
            expr = eq.update(roundOfRealPlusInt.specialize(
                    {x:x_sub, n:n_sub}, assumptions=assumptions))

            return eq.relation
        else:
            raise ValueError("Round operand not of class 'Add'.")

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

# utility function
def _allProvenReals(aTuple, assumptions):
    print("Entering _allProvenReals()")                                         # for testing; delete later
    for elem in aTuple:
        if not InSet(elem, Reals).proven(assumptions=assumptions):
            print("{} not in Reals!".format(elem))                              # for testing; delete later
            return False
    return True

# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(Round, 'roundingElimination',
                                      'roundingEliminated', 'roundingEliminate')
            
