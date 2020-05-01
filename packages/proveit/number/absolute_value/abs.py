from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit._common_ import a, b, x
from proveit.logic import InSet

class Abs(Operation):
    # operator of the Abs operation.
    _operator_ = Literal(stringFormat='Abs', context=__file__)    
    
    def __init__(self, A):
        Operation.__init__(self, Abs._operator_, A)   
    
    def string(self, **kwargs):
        return '|'+self.operand.string()+'|'

    def latex(self, **kwargs):
        return r'\left|'+self.operand.latex()+r'\right|'

    def notEqual(self, rhs, assumptions=USE_DEFAULTS):
        # accessed from conclude() method in not_equals.py 
        from ._theorems_ import absNotEqZero
        from proveit.number import zero
        if rhs == zero:
            return absNotEqZero.specialize(
                    {a:self.operand}, assumptions=assumptions)
        raise ProofFailure(Equals(self, zero), assumptions,
                "'notEqual' only implemented for a right side of zero")

    # def deduceGreaterThanEqualsZero(self, assumptions=frozenset()):
    #     # not yet clear how to update this method
    #     from ._theorems_ import absIsNonNeg
    #     deduceInComplexes(self.operand, assumptions)
    #     return absIsNonNeg.specialize({a:self.operand}).checked(assumptions)

    def deduceGreaterThanEqualsZero(self, assumptions=USE_DEFAULTS):
        # 03/21/2020 wdc: a first attempt at updating this method
        from proveit.number import Complexes
        from ._theorems_ import absIsNonNeg
        # InSet(self.operand, Complexes).prove(assumptions=assumptions)
        return absIsNonNeg.specialize({a:self.operand}, assumptions=assumptions)
    
    # def distribute(self, assumptions=frozenset()):
    #     '''
    #     Distribute the absolute value over a product or fraction.
    #     Assumptions may be needed to deduce that the sub-operands are
    #     complex numbers.
    #     '''
    #     from ._theorems_ import absFrac, absProd
    #     from proveit.number import Div, Mult
    #     if isinstance(self.operand, Div):
    #         deduceInComplexes(self.operand.numerator, assumptions)
    #         deduceInComplexes(self.operand.denominator, assumptions)
    #         return absFrac.specialize({a:self.operand.numerator, b:self.operand.denominator}).checked(assumptions)
    #     elif isinstance(self.operand, Mult):
    #         deduceInComplexes(self.operand.operands, assumptions)
    #         return absProd.specialize({xEtc:self.operand.operands}).checked(assumptions)
    #     else:
    #         raise ValueError('Unsupported operand type for absolution value distribution: ', str(self.operand.__class__))

    def distribute(self, assumptions=USE_DEFAULTS):
        '''
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are
        complex numbers.
        03/21/2020 wdc: a first attempt at updating this method;
        still eliciting an extractInitArgValue error related to a multi-
        variable domain condition for the Mult case. See _demos_ pg
        for an example; WW thinks this is a prob with iterations and
        we'll fix/update this later.
        '''
        from ._theorems_ import absFrac, absProd
        from proveit._common_ import n, xx
        from proveit.number import num, Complexes, Div, Mult
        if isinstance(self.operand, Div):
            return absFrac.specialize(
                    {a:self.operand.numerator, b:self.operand.denominator},
                    assumptions=assumptions)
        elif isinstance(self.operand, Mult):
            from proveit._common_ import xx
            theOperands = self.operand.operands
            return absProd.specialize({n:num(len(theOperands)), xx:theOperands},
                                      assumptions=assumptions)
        else:
            raise ValueError(
                'Unsupported operand type for absolute value distribute() '
                'method: ', str(self.operand.__class__))
    
    def absElimination(self, operand_type = 'non-negative',
                       assumptions=USE_DEFAULTS):
        '''
        For some |x| expression, deduce either |x| = x after trying to
        deduce x >= 0 (for operand_type = 'non_negative' or default) OR
        |x| = -x (for operand_type = 'negative'. Assumptions may be
        needed to deduce x >= 0 or x < 0, respectively.
        '''
        from ._theorems_ import absNonNegElim, absNegElim
        # deduceNonNeg(self.operand, assumptions) # NOT YET IMPLEMENTED
        if operand_type == 'non-negative':
            return absNonNegElim.specialize({x:self.operand},
                                            assumptions=assumptions)
        elif operand_type == 'negative':
            return absNegElim.specialize({x:self.operand},
                                          assumptions=assumptions)
        else:
            raise ValueError(
                "Unsupported operand type for Abs.absElimination() "
                "method; operand type should be specified as "
                "'negative' or 'non-negative', but instead was "
                "operand_type = {}.".format(operand_type))

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        For the case Abs(x) where the operand x is already known to
        be or assumed to be a non-negative real, derive and return 
        this Abs expression equated with the operand itself:
        |- Abs(x) = x. For the case where x is already known or assumed
        to be a negative real, return the Abs expression equated with
        the negative of the operand: |- Abs(x) = -x.
        Assumptions may be necessary to deduce necessary conditions for
        the simplification.
        '''
        from proveit.number import Greater, GreaterEq, Neg
        from proveit.number import (zero, Naturals, NaturalsPos, RealsNeg,
                                    RealsNonNeg, RealsPos)
        # among other things, convert any assumptions=None
        # to assumptions=() (thus averting len(None) errors)
        assumptions = defaults.checkedAssumptions(assumptions)
        print("Entering doReducedSimplification()")                             # for testing; delete later
        print("    The assumptions = {}".format(assumptions))                   # for testing; delete later

        #-- -------------------------------------------------------- --#
        #-- Case (1): Abs(x) where entire operand x is known or      --#
        #--           assumed to be non-negative Real.               --#
        #-- -------------------------------------------------------- --#
        if InSet(self.operand, RealsNonNeg).proven(assumptions=assumptions):
            # Entire operand is known to be or assumed to be a
            # non-negative real, so we can return Abs(x) = x
            return self.absElimination(operand_type='non-negative',
                                       assumptions=assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (2): Abs(x) where entire operand x is known or      --#
        #--           assumed to be a negative Real.                 --#
        #-- -------------------------------------------------------- --#
        if InSet(self.operand, RealsNeg).proven(assumptions=assumptions):
            # Entire operand is known to be or assumed to be a
            # negative real, so we can return Abs(x) = -x
            return self.absElimination(operand_type='negative',
                                       assumptions=assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (3): Abs(x) where entire operand x is not yet known --*
        #--           to be a non-negative Real, but can EASILY be   --#
        #--           proven to be a non-negative Real because it is --#
        #--           known or assumed to be ≥ 0 or known or assumed --#
        #--           to be in a subset of the non-negative Reals    --#
        #-- -------------------------------------------------------- --#
        print("self.operand = {}".format(self.operand))                         # for testing; delete later
        print("assumptions = {}".format(assumptions))                           # for testing; delete later
        if (Greater(self.operand, zero).proven(assumptions=assumptions) or
            GreaterEq(self.operand, zero).proven(assumptions=assumptions)):
            print("Inside the Greater/GreaterEq If")                            # for testing; delete later
            GreaterEq(self.operand, zero).prove(assumptions=assumptions)
            from proveit.number.sets.real._theorems_ import (
                    inRealsNonNegIfGreaterEqZero)
            inRealsNonNegIfGreaterEqZero.specialize(
                {a: self.operand}, assumptions=assumptions)
            return self.absElimination(operand_type='non-negative',
                                       assumptions=assumptions)

        if self.operand in InSet.knownMemberships.keys():
            from proveit.logic.set_theory import Subset, SubsetEq
            for kt in InSet.knownMemberships[self.operand]:
                if kt.isSufficient(assumptions):
                    if (SubsetEq(kt.expr.operands[1], Naturals).proven(assumptions)
                        or 
                        Subset(kt.expr.operands[1], NaturalsPos).proven(assumptions)
                        or 
                        Subset(kt.expr.operands[1], RealsPos).proven(assumptions)):
                        InSet(self.operand, RealsNonNeg).prove()
                        return self.absElimination(operand_type='non-negative',
                                                   assumptions=assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (4): Abs(x) where entire operand x is not yet known --*
        #--           to be a negative Real, but can EASILY be       --#
        #--           proven to be a negative Real because it -x is  --#
        #--           known to be in a subset of the positive Reals  --#
        #-- -------------------------------------------------------- --#
        print("self.operand = {}".format(self.operand))                         # for testing; delete later
        negOp = Neg(self.operand)
        print("negOp = {}".format(negOp))                                       # for testing; delete later
        negOpSimp = negOp.simplification(assumptions=assumptions)
        print("negOpSimp = {}".format(negOpSimp))                               # for testing; delete later
        print("negOpSimp.rhs = {}".format(negOpSimp.rhs))                       # for testing; delete later
        negated_op = Neg(self.operand).simplification().rhs
        print("negated_op = {}".format(negated_op))                             # for testing; delete later
        if negated_op in InSet.knownMemberships.keys():
            from proveit.logic.set_theory import Subset, SubsetEq
            from proveit.number.sets.real._theorems_ import (
                    negInRealsNegIfPosInRealsPos)
            for kt in InSet.knownMemberships[negated_op]:
                print("    kt = {}".format(kt))                                 # for testing; delete later
                if kt.isSufficient(assumptions):
                    print("    kt.expr = {}".format(kt.expr))                   # for testing; delete later
                    print("    kt.expr.operands[1] = {}".format(kt.expr.operands[1])) # for testing; delete later
                    if (SubsetEq(kt.expr.operands[1], NaturalsPos).proven(assumptions)
                        or 
                        Subset(kt.expr.operands[1], NaturalsPos).proven(assumptions)
                        or
                        SubsetEq(kt.expr.operands[1], RealsPos).proven(assumptions)
                        or
                        Subset(kt.expr.operands[1], RealsPos).proven(assumptions)):
                        InSet(negated_op, RealsPos).prove()
                        print("Proved negated_op is positive Real.")            # for testing; delete later
                        negInRealsNegIfPosInRealsPos.specialize({a:negated_op}, assumptions=assumptions)
                        print("Specialization done.")                           # for testing; delete later
                        return self.absElimination(operand_type='negative',
                                                   assumptions=assumptions)

        # for updating our equivalence claim(s) for the
        # remaining possibilities
        from proveit import TransRelUpdater
        eq = TransRelUpdater(self, assumptions)
        return eq.relation



    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integers, Reals, etc),
        attempt to prove that the given expression is in that number
        set using the appropriate closure theorem.
        '''
        from proveit.number.absolute_value._theorems_ import (
                  absComplexClosure, absNonzeroClosure,
                  absComplexClosureNonNegReals)
        from proveit.number import Complexes, Reals, RealsNonNeg, RealsPos

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Reals:
            return absComplexClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsPos:
            return absNonzeroClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsNonNeg:
            return absComplexClosureNonNegReals.specialize({a:self.operand},
                      assumptions=assumptions)

        msg = ("'Abs.deduceInNumberSet()' not implemented for "
               "the %s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
