from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit._common_ import a, b, x
from proveit.logic import InSet
from proveit.logic.set_theory import ProperSubset, SubsetEq
from proveit.number import Add, Mult

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

    def deduceGreaterThanEqualsZero(self, assumptions=USE_DEFAULTS):
        from proveit.number import Complexes
        from ._theorems_ import absIsNonNeg
        return absIsNonNeg.specialize({a:self.operand}, assumptions=assumptions)

    def distribute(self, assumptions=USE_DEFAULTS):
        '''
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are
        complex numbers.
        This works fine for the Abs(Div()) case, but still
        eliciting an extractInitArgValue error related to a multi-
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
            return absProd.specialize(
                    {n:num(len(theOperands)), xx:theOperands},
                    assumptions=assumptions)
        else:
            raise ValueError(
                'Unsupported operand type for Abs.distribute() '
                'method: ', str(self.operand.__class__))

    def absElimination(self, operand_type = None, assumptions=USE_DEFAULTS):
        '''
        For some |x| expression, deduce either |x| = x (the default) OR
        |x| = -x (for operand_type = 'negative'). Assumptions may be
        needed to deduce x >= 0 or x < 0, respectively.
        '''

        from proveit.number import Neg
        from ._theorems_ import absNonNegElim, absNegElim
        # deduceNonNeg(self.operand, assumptions) # NOT YET IMPLEMENTED
        if operand_type == None or operand_type == 'non-negative':
            return absNonNegElim.specialize({x:self.operand},
                                            assumptions=assumptions)
        elif operand_type == 'negative':
            return absNegElim.specialize({x:self.operand},
                                          assumptions=assumptions)
        else:
            raise ValueError(
                "Unsupported operand type for Abs.absElimination() "
                "method; operand type should be omitted or specified "
                "as 'negative' or 'non-negative', but instead was "
                "given as operand_type = {}.".format(operand_type))

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
        from proveit.number import Greater, GreaterEq, Mult, Neg
        from proveit.number import (zero, Naturals, NaturalsPos, RealsNeg,
                                    RealsNonNeg, RealsPos)
        # among other things, convert any assumptions=None
        # to assumptions=() (thus averting len(None) errors)
        assumptions = defaults.checkedAssumptions(assumptions)

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
        #--           to be a non-negative Real, but can easily be   --#
        #--           proven to be a non-negative Real because it is --#
        #--           (a) known or assumed to be ≥ 0 or
        #--           (b) known or assumed to be in a subset of the  --#
        #--               non-negative Reals, or                     --#
        #--           (c) the addition or product of operands, all   --#
        #--               of which are known or assumed to be non-   --#
        #--               negative reals. TBA!
        #-- -------------------------------------------------------- --#
        if (Greater(self.operand, zero).proven(assumptions=assumptions) and
            not GreaterEq(self.operand, zero).proven(assumptions=assumptions)):
            GreaterEq(self.operand, zero).prove(assumptions=assumptions)
            # and then it will get picked up in the next if() below

        if GreaterEq(self.operand, zero).proven(assumptions=assumptions):
            from proveit.number.sets.real._theorems_ import (
                    inRealsNonNegIfGreaterEqZero)
            inRealsNonNegIfGreaterEqZero.specialize(
                {a: self.operand}, assumptions=assumptions)
            return self.absElimination(operand_type='non-negative',
                                       assumptions=assumptions)

        if self.operand in InSet.knownMemberships.keys():
            for kt in InSet.knownMemberships[self.operand]:
                if kt.isSufficient(assumptions):
                    if isEqualToOrSubsetEqOf(
                            kt.expr.operands[1],
                            equal_sets=[RealsNonNeg, RealsPos],
                            subset_eq_sets=[Naturals, NaturalsPos, RealsPos],
                            assumptions=assumptions):

                        InSet(self.operand, RealsNonNeg).prove(
                                assumptions=assumptions)
                        return self.absElimination(operand_type='non-negative',
                                                   assumptions=assumptions)

        if isinstance(self.operand, Add) or isinstance(self.operand, Mult):
            count_of_known_memberships = 0
            count_of_known_relevant_memberships = 0
            for op in self.operand.operands:
                if op in InSet.knownMemberships.keys():
                    count_of_known_memberships += 1
            if count_of_known_memberships == len(self.operand.operands):
                for op in self.operand.operands:
                    op_temp_known_memberships = InSet.knownMemberships[op]
                    for kt in op_temp_known_memberships:
                        if (kt.isSufficient(assumptions)
                            and isEqualToOrSubsetEqOf(
                                        kt.expr.operands[1],
                                        equal_sets=[RealsNonNeg, RealsPos],
                                        subset_eq_sets=[Naturals, NaturalsPos,
                                                RealsPos, RealsNonNeg],
                                        assumptions=assumptions)):

                            count_of_known_relevant_memberships += 1
                            break

                if (count_of_known_relevant_memberships ==
                        len(self.operand.operands)):
                    # Prove that the sum or product is in
                    # RealsNonNeg and then instantiate absElimination.
                    for op in self.operand.operands:
                        InSet(op, RealsNonNeg).prove(assumptions=assumptions)
                    return self.absElimination(assumptions=assumptions)


        #-- -------------------------------------------------------- --#
        #-- Case (4): Abs(x) where operand x can easily be proven    --#
        #--           to be a negative Real because -x is known to   --#
        #--           be in a subset of the positive Reals           --#
        #-- -------------------------------------------------------- --#
        negated_op = None
        if isinstance(self.operand, Neg):
            negated_op = self.operand.operand
        else:
            negated_op = Neg(self.operand)
        negated_op_simp = negated_op.simplification(assumptions=assumptions).rhs

        if negated_op_simp in InSet.knownMemberships.keys():
            from proveit.number.sets.real._theorems_ import (
                    negInRealsNegIfPosInRealsPos)
            for kt in InSet.knownMemberships[negated_op_simp]:
                if kt.isSufficient(assumptions):
                    if isEqualToOrSubsetEqOf(
                            kt.expr.operands[1],
                            equal_sets=[RealsNonNeg, RealsPos],
                            subset_sets=[NaturalsPos, RealsPos],
                            subset_eq_sets=[NaturalsPos, RealsPos],
                            assumptions=assumptions):

                        InSet(negated_op_simp, RealsPos).prove(
                                assumptions=assumptions)
                        negInRealsNegIfPosInRealsPos.specialize(
                            {a:negated_op_simp}, assumptions=assumptions)
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

        # To be thorough and a little more general, we check if the
        # specified number_set is already proven to *contain* one of
        # the number sets we have theorems for -- for example,
        #     Y=Complexes contain X=Reals, and
        #     Y=(-1, inf) contains X=RealsPos,
        # but we don't have specific thms for those supersets Y.
        # If so, use the appropiate thm to determine that self is in X,
        # then prove that self must also be in Y since Y contains X.
        if SubsetEq(Reals, number_set).proven(assumptions=assumptions):
            absComplexClosure.specialize({a:self.operand},
                      assumptions=assumptions)
            return InSet(self, number_set).prove(assumptions=assumptions)
        if SubsetEq(RealsPos, number_set).proven(assumptions=assumptions):
            absNonzeroClosure.specialize({a:self.operand},
                      assumptions=assumptions)
            return InSet(self, number_set).prove(assumptions=assumptions)
        if SubsetEq(RealsNonNeg, number_set).proven(assumptions=assumptions):
            absComplexClosureNonNegReals.specialize({a:self.operand},
                      assumptions=assumptions)
            return InSet(self, number_set).prove(assumptions=assumptions)


        # otherwise, we just don't have the right thm to make it work
        msg = ("'Abs.deduceInNumberSet()' not implemented for "
               "the %s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)

def isEqualToOrSubsetEqOf(
        number_set, equal_sets=None, subset_sets=None, subset_eq_sets=None,
        assumptions=None):
    '''
    A utility function used in the doReducedSimplification() method
    to test whether the number set specified by number_set:
    • is equal to any of the number sets provided in the list of
      equal_sets
    • OR is already known/proven to be a proper subset of any of the
      number sets provided in the list of subset_sets,
    • OR is already known/proven to be an improper subset of any of the
      number sets provided in the list of subset_eq_sets,
    returning True at the first such equality, subset, or subset_eq
    relation found to be True.
    '''
    # among other things, convert any assumptions=None
    # to assumptions=() (thus averting len(None) errors)
    assumptions = defaults.checkedAssumptions(assumptions)

    if not equal_sets == None:
        for temp_set in equal_sets:
            if number_set == temp_set:
                return True
    if not subset_eq_sets == None:
        for temp_set in subset_eq_sets:
            if SubsetEq(number_set, temp_set).proven(assumptions):
                return True
    if not subset_sets == None:
        for temp_set in subset_sets:
            if ProperSubset(number_set, temp_set).proven(assumptions):
                return True
    return False
