from proveit import (Literal, Operation, USE_DEFAULTS, ExprTuple,
                     ProofFailure, InnerExpr)
from proveit.logic import Equals, InSet
from proveit.number import num
from proveit.number.sets import (Integers, Naturals, NaturalsPos, Reals,
                                 RealsNonNeg, RealsPos, Complexes)
import proveit.number.numeral.deci
from proveit.number.numeral.deci import DIGITS
from proveit._common_ import a, b, c, d, i, j, k, m, n, w, x, y, z
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, groupCommutation, pairwiseEvaluation
from proveit import TransRelUpdater


class Mult(Operation):
    # operator of the Mult operation.
    _operator_ = Literal(stringFormat='*', latexFormat=r'\cdot', context=__file__)

    # Multiplying two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    multipliedNumerals = set()

    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        Operation.__init__(self, Mult._operator_, operands)
        self.factors = operands
        if len(self.factors)==2 and all(factor in DIGITS for factor in self.factors):
            if self not in Mult.multipliedNumerals:
                try:
                    # for single digit addition, import the theorem that provides the evaluation
                    Mult.multipliedNumerals.add(self)
                    proveit.number.numeral.deci._theorems_.__getattr__('mult_%d_%d'%(self.factors[0].asInt(), self.factors[1].asInt()))
                except:
                    # may fail before the relevent _commons_ and _theorems_ have been generated
                    pass # and that's okay

    def deduceInNumberSet(self, numberSet, assumptions=USE_DEFAULTS):
        # edited by JML 7/20/19
        from ._theorems_ import (multIntClosure, multIntClosureBin,
            multNatClosure, multNatClosureBin,
            multNatPosClosure, multNatPosClosureBin,
            multRealClosure, multRealClosureBin, multRealPosClosure,
            multRealPosClosureBin,
            multRealNonNegClosure, multRealNonNegClosureBin,
            multComplexClosure, multComplexClosureBin)
        if hasattr(self, 'number_set'):
            numberSet = numberSet.number_set
        bin = False
        if numberSet == Integers:
            if len(self.operands) == 2:
                thm = multIntClosureBin
                bin = True
            else:
                thm = multIntClosure
        elif numberSet == Naturals:
            if len(self.operands) == 2:
                thm = multNatClosureBin
                bin = True
            else:
                thm = multNatClosure
        elif numberSet == NaturalsPos:
            if len(self.operands) == 2:
                thm = multNatPosClosureBin
                bin = True
            else:
                thm = multNatPosClosure
        elif numberSet == Reals:
            if len(self.operands) == 2:
                thm = multRealClosureBin
                bin = True
            else:
                thm = multRealClosure
        elif numberSet == RealsPos:
            if len(self.operands) == 2:
                thm = multRealPosClosureBin
                bin = True
            else:
                thm = multRealPosClosure
        elif numberSet == Complexes:
            if len(self.operands) == 2:
                thm = multComplexClosureBin
                bin = True
            else:
                thm = multComplexClosure
        elif numberSet == RealsNonNeg:
            if len(self.operands) == 2:
                thm = multRealNonNegClosureBin
                bin = True
            else:
                thm = multRealNonNegClosure
        else:
            msg = ("'Mult.deduceInNumberSet()' not implemented for the "
                   "%s set"%str(numberSet))
            raise ProofFailure(InSet(self, numberSet), assumptions, msg)
        # print("thm", thm)
        # print("self in deduce in number set", self)
        # print("self.operands", self.operands)
        if bin:
            return thm.specialize({a:self.operands[0], b:self.operands[1]},
                                  assumptions=assumptions)
        return thm.specialize({n:self.operands.length(assumptions),
                               a:self.operands},
                              assumptions=assumptions)

    def deduceDividedBy(self, divisor, assumptions=USE_DEFAULTS):
        '''
        Deduce that the product represented by Mult(a,b) is divisible
        by the mult_factor a or b. For example,
           Mult(a, b).deduceDividedBy(a)
        returns |- Divides(a, Mult(a,b)), that is |- a|ab, (assuming
        complex a≠0 and integer b).
        Later: possibly consider an Equals(divisor,self.lhs) case?
        '''
        if divisor==self.operands[0]: # a|ab
            from proveit.number.divisibility._theorems_ import (
                    leftFactorDivisibility)
            _x, _y = leftFactorDivisibility.instanceParams
            return leftFactorDivisibility.instantiate(
                    {_x:self.operands[0], _y:self.operands[1]},
                    assumptions=assumptions)

        elif divisor==self.operands[1]: # a|ba
            from proveit.number.divisibility._theorems_ import (
                    rightFactorDivisibility)
            _x, _y = rightFactorDivisibility.instanceParams
            return rightFactorDivisibility.instantiate(
                    {_x:self.operands[0], _y:self.operands[1]},
                    assumptions=assumptions)

        else:
            raise ValueError(
                    "In Mult({0}, {1}).deduceDividedBy({2}), "
                    "the supplied divisor {2} does not appear "
                    "to be equal to either of the multiplicands "
                    "{0} or {1}.".
                    format(self.operands[0], self.operands[1], divisor))


    def notEqual(self, rhs, assumptions=USE_DEFAULTS):
        from ._theorems_ import multNotEqZero
        from proveit.number import zero
        if rhs == zero:
            _n = self.operands.length(assumptions)
            _a = self.operands
            return multNotEqZero.specialize({n:_n, a:_a},
                                            assumptions=assumptions)
        raise ProofFailure(Equals(self, zero), assumptions, (
                "'notEqual' only implemented for a right side of zero"))

    def doReducedSimplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Derive and return this multiplication expression equated with a simpler form.
        Deals with disassociating any nested multiplications,simplifying negations, and
        factors of one, in that order.
        doReducedEvaluation deals with factors of 0.
        '''

        expr = self
        eq = TransRelUpdater(self, assumptions) # for convenience updating our equation

        # Ungroup the expression (disassociate nested multiplications).
        idx = 0
        length = len(expr.operands) - 1
        while idx < length:
            # loop through all operands
            if isinstance(expr.operands[idx], Mult):
                # if it is grouped, ungroup it
                expr = eq.update(expr.disassociation(idx, assumptions))
            else:
                idx += 1
            length = len(expr.operands)

        # Simplify negations -- factor them out.
        expr = eq.update(expr.negSimplifications(assumptions))

        if not isinstance(expr, Mult):
            # The expression may have changed to a negation after doing
            # negSimplification.  Start the simplification of this new
            # expression fresh at this point.
            eq.update(expr.simplification(assumptions))
            return eq.relation

        # Eliminate any factors of one.
        expr = eq.update(expr.oneEliminations(assumptions))

        return eq.relation

    def negSimplifications(self, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        negated factors are factored out.  For example:
            (-w)*(-x)*y*(-z) = -(w*x*y*z)
        '''
        from proveit.number import Neg

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands)):
            if isinstance(operand, Neg):
                idx = len(self.operands) - rev_idx - 1
                if isinstance(expr, Mult):
                    expr = eq.update(expr.negSimplification(idx, assumptions))
                elif isinstance(expr, Neg):
                    expr = eq.update(expr.innerNegMultSimplification(idx, assumptions))

        return eq.relation

    def negSimplification(self, idx, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        a specific negated factor, at the given index, is factored out.
        For example:
            w*(-x)*y*z = -(w*x*y*z)
        '''
        from proveit.number import Neg
        from ._theorems_ import multNegLeft, multNegRight, multNegAny

        if not isinstance(self.operands[idx], Neg):
            raise ValueError("Operand at the index %d expected to be a negation for %s"%(idx, str(self)))

        if len(self.operands)==2:
            if idx==0:
                _x = self.operands[0].operand
                _y = self.operands[1]
                return multNegLeft.specialize({x:_x, y:_y},
                                              assumptions=assumptions)
            else:
                _x = self.operands[0]
                _y = self.operands[1].operand
                return multNegRight.specialize({x:_x, y:_y},
                                               assumptions=assumptions)
        _a = ExprTuple(*self.operands[:idx])
        _b = self.operands[idx].operand
        _c = ExprTuple(*self.operands[idx+1:])
        _i = _a.length(assumptions)
        _j = _c.length(assumptions)
        return multNegAny.specialize({i:_i, j:_j, a:_a, b:_b, c:_c},
                                     assumptions=assumptions)

    def oneEliminations(self, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        factors of one are eliminated.  For example:
            x*1*y*1*z*1 = x*y*z
        '''
        from proveit.number import one

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands)):
            if operand==one:
                idx = len(self.operands) - rev_idx - 1
                expr = eq.update(expr.oneElimination(idx, assumptions))
                if not isinstance(expr, Mult):
                    break # can't do an elimination if reduced to a single term.

        return eq.relation

    def oneElimination(self, idx, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        a single factor of one, at the given index, is eliminated.
        For example:
            x*y*1*z = x*y*z
        '''
        from proveit.number import one
        from ._theorems_ import elimOneLeft, elimOneRight, elimOneAny

        if self.operands[idx] != one:
            raise ValueError("Operand at the index %d expected to be zero for %s"%(idx, str(self)))

        if len(self.operands)==2:
            if idx==0:
                return elimOneLeft.specialize({x:self.operands[1]},
                                               assumptions=assumptions)
            else:
                return elimOneRight.specialize({x:self.operands[0]},
                                                assumptions=assumptions)
        _a = ExprTuple(*self.operands[:idx])
        _b = ExprTuple(*self.operands[idx+1:])
        _i = _a.length(assumptions)
        _j = _b.length(assumptions)
        return elimOneAny.specialize({i:_i, j:_j, a:_a, b:_b},
                                     assumptions=assumptions)

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Derive and return this multiplication expression equated with an irreducible value.
        Handle the trivial case of a zero factor or do pairwise evaluation
        after simplifying negations and eliminating one factors.
        '''
        from ._theorems_ import multZeroLeft, multZeroRight, multZeroAny
        from proveit.logic import isIrreducibleValue, EvaluationError
        from proveit.number import zero

        # First check for any zero factors -- quickest way to do an evaluation.
        try:
            zeroIdx = self.operands.index(zero)
            if len(self.operands)==2:
                if zeroIdx==0:
                    return multZeroLeft.specialize({x:self.operands[1]}, assumptions=assumptions)
                else:
                    return multZeroRight.specialize({x:self.operands[0]}, assumptions=assumptions)
            _a = self.operands[:zeroIdx]
            _b = self.operands[zeroIdx+1:]
            _i = ExprTuple(*_a.length(assumptions))
            _j = ExprTuple(*_b.length(assumptions))
            return multZeroAny.specialize({i:_i, j:_j, a:_a, b:_b},
                                          assumptions=assumptions)
        except (ValueError, ProofFailure):
            pass # No such "luck" regarding a simple multiplication by zero.

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Simplify negations -- factor them out.
        expr = eq.update(expr.negSimplifications(assumptions))

        if not isinstance(expr, Mult):
            # The expression may have changed to a negation after doing
            # negSimplification.  Start the simplification of this new
            # expression fresh at this point.
            eq.update(expr.evaluation(assumptions))
            return eq.relation

        # Eliminate any factors of one.
        expr = eq.update(expr.oneEliminations(assumptions))

        if isIrreducibleValue(expr):
            return eq.relation # done

        if len(self.operands) > 2:
            eq.update(pairwiseEvaluation(expr, assumptions))
            return eq.relation

        raise EvaluationError(self, assumptions)

    def conversionToAddition(self, assumptions=USE_DEFAULTS):
        '''
        From multiplication by an integer as the first factor,
        derive and return the equivalence of this multiplication
        to a repeated addition; for example, 3*c = c + c + c.
        '''
        from ._axioms_ import multDef
        if hasattr(self.operands[0], 'asInt'):
            reps = self.operands[0].asInt()
        else:
            raise ValueError("Cannot 'expandAsAddition' unless the first operand is a literal integer: %s"%str(self))

        expr = self
        eq = TransRelUpdater(self, assumptions) # for convenience updating our equation
        # Group together the remaining factors if necessary:
        if len(self.operands) > 2:
            expr = eq.update(expr.association(1, len(self.operands)-1, assumptions))
        _x = self.operands[1]
        _n = num(reps)
        eq.update(multDef.specialize({n:_n, a:[_x]*reps, x:_x},
                                      assumptions=assumptions))
        return eq.relation

    def index(self, theFactor, alsoReturnNum=False):
        '''
        Return the starting index of theFactor, which may be a single operand,
        a list of consecutive operands, or a Mult expression that represents
        the product of the list of consecutive operands.  If alsoReturnNum is
        True, return a tuple of the index and number of operands for theFactor.
        '''
        if isinstance(theFactor, Mult):
            theFactor = theFactor.operands
        if hasattr(theFactor, '__getitem__') and hasattr(theFactor, '__len__'):
            # multiple operands in theFactor
            firstFactor = theFactor[0]
            num = len(theFactor)
            idx = -1
            try:
                while True:
                    idx = self.operands.index(firstFactor, start=idx+1)
                    if tuple(self.operands[idx:idx+num]) == tuple(theFactor):
                        break # found it all!
            except ValueError:
                raise ValueError("Factor is absent!")
        else:
            num = 1
            try:
                idx = self.operands.index(theFactor)
            except ValueError:
                raise ValueError("Factor is absent!")
        return (idx, num) if alsoReturnNum else idx

    def pull(self, startIdx=None, endIdx=None, direction='left', assumptions=USE_DEFAULTS):
        '''
        Pull a subset of consecutive operands, self.operands[startIdx:endIdx],
        to one side or another. Returns the equality that equates self to
        this new version.  Give any assumptions necessary to prove that the
        operands are in Complexes so that the commutation theorem is applicable.
        '''
        if direction == "left": # pull the factor(s) to the left
            if startIdx == 0 or startIdx is None:
                return Equals(self, self).prove(assumptions) # no move necessary
            return self.groupCommutation(None, startIdx, startIdx, endIdx, assumptions=assumptions)
        elif direction == "right": # pull the factor(s) to the right
            if endIdx == len(self.operands) or endIdx is None:
                return Equals(self, self).prove(assumptions) # no move necessary
            return self.groupCommutation(startIdx, endIdx, endIdx, None, assumptions=assumptions)
        else:
            raise ValueError("Invalid pull direction!  (Acceptable values are \"left\" and \"right\".)")

    def distribution(self, idx=None, assumptions=USE_DEFAULTS):
        r'''
        Distribute through the operand at the given index.
        Returns the equality that equates self to this new version.
        Examples:
            :math:`a (b + c + a) d = a b d + a c d + a a d`
            :math:`a (b - c) d = a b d - a c d`
            :math:`a \left(\sum_x f(x)\right c = \sum_x a f(x) c`
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from ._theorems_ import distributeThroughSum, distributeThroughSubtract#, distributeThroughSummation
        from proveit.number.division._theorems_ import prodOfFracs #, fracInProd
        from proveit.number import Add, Div, Neg, Sum
        if idx is None and len(self.factors) == 2 and all(isinstance(factor, Div) for factor in self.factors):
            return prodOfFracs.specialize({x:self.factors[0].numerator, y:self.factors[1].numerator, z:self.factors[0].denominator, w:self.factors[1].denominator}, assumptions=assumptions)
        operand = self.operands[idx]
        _a = ExprTuple(*self.operands[:idx])
        _c = ExprTuple(*self.operands[idx+1:])
        _i = _a.length(assumptions)
        _k = _c.length(assumptions)
        if isinstance(operand, Add):
            _b = self.operands[idx].operands
            _j = _b.length(assumptions)
            return distributeThroughSum.specialize(
                    {i:_i, j:_j, k:_k, a:_a, b:_b, c:_c},
                    assumptions=assumptions)
        elif (isinstance(operand, Add) and len(operand.operands)==2
                  and isinstance(operand.operands[0], Neg)):
            _j = _k
            _x = self.operands[idx].operands[0]
            _y = self.operands[idx].operands[1].operand
            return distributeThroughSubtract.specialize(
                    {i:_i, j:_j, a:_a, x:_x, y:_y, c:_c},
                    assumptions=assumptions)
        elif isinstance(operand, Div):
            raise NotImplementedError("Mult.distribution must be updated "
                                      "for Div case.")
            '''
            eqn = fracInProd.specialize({wMulti:self.operands[:idx], x:self.operands[idx].operands[0], y:self.operands[idx].operands[1], zMulti:self.operands[idx+1:]}, assumptions=assumptions)
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numerSimplification = eqn.rhs.numerator.simplification(assumptions=assumptions)
                dummyVar = eqn.safeDummyVar()
                return numerSimplification.subRightSideInto(Equals(eqn.lhs, frac(dummyVar, eqn.rhs.denominator)), dummyVar)
            except:
                return eqn
            '''
        elif isinstance(operand, Sum):
            raise NotImplementedError("Mult.distribution must be updated "
                                      "for Sum case.")
            '''
            yMultiSub = operand.indices
            Pop, Pop_sub = Operation(P, operand.indices), operand.summand
            S_sub = operand.domain
            xDummy, zDummy = self.safeDummyVars(2)
            spec1 = distributeThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yMulti:yMultiSub,
                                                           xMulti:Etcetera(MultiVariable(xDummy)), zMulti:Etcetera(MultiVariable(zDummy))}, assumptions=assumptions)
            return spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):self.operands[:idx], \
                                                        Etcetera(MultiVariable(zDummy)):self.operands[idx+1:]}, assumptions=assumptions)
            '''
        else:
            raise Exception("Unsupported operand type to distribute over: " + str(operand.__class__))

    def factorization(self,theFactor,pull="left", groupFactor=True, groupRemainder=False, assumptions=USE_DEFAULTS):
        '''
        Factor out "theFactor" from this product, pulling it either to the "left" or "right".
        If "theFactor" is a product, this may factor out a subset of the operands as
        long as they are next to each other (use commute to make this happen).  If
        there are multiple occurrences, the first occurrence is used.  If groupFactor is
        True and theFactor is a product, these operands are grouped together as a sub-product.
        If groupRemainder is True and there are multiple remaining operands (those not in
        "theFactor"), then these remaining operands are grouped together as a sub-product.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        expr = self
        eq = TransRelUpdater(expr, assumptions)
        idx, num = self.index(theFactor, alsoReturnNum=True)
        expr = eq.update(self.groupCommutation(
                idx, 0 if pull=='left' else -num, length=num,
                assumptions=assumptions))
        if groupFactor and num > 1:
            if pull == 'left':  # use 0:num type of convention like standard pythong
                expr = eq.update(expr.association(0, num,
                                                  assumptions=assumptions))
            elif pull == 'right':
                expr = eq.update(expr.association(-num, num,
                                                  assumptions=assumptions))
        if groupRemainder and len(self.operands)-num > 1:
            # if the factor has been group, effectively there is just 1 factor operand now
            num_factor_operands = 1 if groupFactor else num
            if pull == 'left':
                expr = eq.update(expr.association(num_factor_operands,
                                                  len(self.operands)-num_factor_operands,
                                                  assumptions=assumptions))
            elif pull == 'right':
                expr = eq.update(expr.association(0, num_factor_operands,
                                                  assumptions=assumptions))
        return eq.relation

    def exponentCombination(self, startIdx=None, endIdx=None,
                            assumptions=USE_DEFAULTS):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$,
        $a^b a$ to $a^{b+1}, $a a^b$ to $a^{1+b}, or
        $a^c b^c$ to $(a b)^c$.
        '''
        from proveit import ExprRange, free_vars
        from proveit.logic import And
        from proveit.number.exponentiation._theorems_ import (
                product_of_posnat_powers, products_of_posnat_powers,
                product_of_pos_powers, products_of_pos_powers,
                product_of_real_powers, products_of_real_powers,
                product_of_complex_powers, products_of_complex_powers)
        #from proveit.number.exponentiation._theorems_ import (
        #        sumInExp, diffInExp, diffFracInExp)
        from proveit.number.exponentiation._theorems_ import (
                addOneRightInExp, addOneLeftInExp)
        from proveit.number import Exp
        if startIdx is not None or endIdx is not None:
            dummyVar = self.safeDummyVar()
            grouped = self.group(startIdx, endIdx, assumptions=assumptions)
            innerCombination = (
                grouped.rhs.factors[startIdx].
                exponentCombination(assumptions=assumptions))
            combineInGroup = (
                innerCombination.
                substitution(Mult(*(self.factors[:startIdx]
                                    + (dummyVar,)
                                    + self.factors[endIdx:])), dummyVar))
            return grouped.applyTransitivity(combineInGroup)
        # if all(isinstance(factor, Sqrt) for factor in self.factors):
        #     # combine the square roots into one square root
        #     factorBases = [factor.base for factor in self.factors]
        #     return prodOfSqrts.specialize({xMulti:factorBases},
        #                                   assumptions=assumptions)
        # the following sqrt specialization modified by wdc on 2/29/2020
        # based on the above-commented-out code (kept here temporarily
        # until we're sure this works ok)
        
        exp_operand_msg = (
                'Combine exponents only implemented for a product '
                'of two exponentiated operands (or a simple variant)')
        
        if not self.operands.is_binary() or not isinstance(self.operands[0], Exp) or not isinstance(self.operands[1], Exp):
            if self.operands.is_binary() and isinstance(self.operands[0], Exp) and self.operands[0].base == self.operands[1]:
                # Of the form a^b a
                return addOneRightInExp.specialize({a:self.operands[1], b:self.operands[0].exponent}, assumptions=assumptions).deriveReversed(assumptions)
            elif self.operands.is_binary() and isinstance(self.operands[1], Exp) and self.operands[1].base == self.operands[0]:
                # Of the form a a^b
                return addOneLeftInExp.specialize({a:self.operands[0], b:self.operands[1].exponent}, assumptions=assumptions).deriveReversed(assumptions)
            raise NotImplementedError("Need to better implement degenerate cases "
                                      "of a^b*a and a*a^b.")                 
            #raise ValueError(exp_operand_msg)
        
        # Create a list of bases and ranges of bases,
        # and a list of exponents and ranges of exponents,
        # and determine if all of the represented bases are the same
        # or if all of the represented exponents are the same.
        # For example, 
        #   (a_1^c * ... * a_n^c * b^c)
        # would result in:
        #   same_base=False, same_exponent=c,
        #   operand_bases = [a_1, ..., a_n, b]
        #   operand_exonents = [c, ..n repeats.. c, c]
        operand_bases = []
        operand_exponents = []
        same_base = None
        same_exponent = None
        for operand in self.operands:
            if isinstance(operand, ExprRange):
                if not isinstance(operand.body, Exp):
                    raise ValueError(exp_operand_msg)
                operand_bases.append(operand.mapped_range(
                        lambda exponential : exponential.base))
                operand_exponents.append(operand.mapped_range(
                        lambda exponential : exponential.exponent))
                base = operand_bases.innermost_body()
                exponent = operand_exponents.innermost_body()
                operand_parameters = operand.parameters()
                if not free_vars(base, err_inclusively=True).isdisjoint(
                        operand_parameters):
                    # Can't have the same base unless the base
                    # is independent of range parameters.
                    same_base = False
                if not free_vars(exponent, err_inclusively=True).isdisjoint(
                        operand_parameters):
                    # Can't have the same exponent unless the exponent
                    # is independent of range parameters.
                    same_exponent = False
            else:
                if not isinstance(operand, Exp):
                    raise ValueError(exp_operand_msg)
                base = operand.base
                exponent = operand.exponent
                operand_bases.append(base)
                operand_exponents.append(exponent)
            if same_base is None:
                same_base = base
            elif same_base != base:
                # Not all bases are the same
                same_base = False
            if same_exponent is None:
                same_exponent = base
            elif same_exponent != base:
                # Not all exponents are the same
                same_exponent = False
        
        if same_base not in (None, False):
            # Same base: a^b a^c = a^{b+c}$, or something similar
            
            # Find out the known type of the exponents.
            possible_exponent_types = [NaturalsPos, RealsPos, Reals,
                                       Complexes]
            for exponent in operand_exponents:
                while len(possible_exponent_types) > 1:
                    exponent_type = possible_exponent_types[0]
                    if isinstance(exponent, ExprRange):
                        in_sets = exponent.mapped_range(
                                lambda exp_range_body : 
                                    InSet(exp_range_body, exponent_type))
                        if And(in_sets).proven(assumptions):
                            # This type is known for these exponents.
                            break
                    else:
                        if InSet(exponent, exponent_type).proven(assumptions):
                            # This type is known for this exponent.
                            break
                    # We've eliminated a type from being known. 
                    possible_exponent_types.pop(0)
            known_exponent_type = possible_exponent_types[0]
            
            if known_exponent_type == NaturalsPos:
                if self.base.operands.is_binary():
                    _m, _n = operand_exponents
                    return product_of_posnat_powers.instantiate(
                            {a:same_base, m:_m, n:_n}, assumptions=assumptions)
                else:
                    _k = ExprTuple(*operand_exponents)
                    _m = _k.length(assumptions)                    
                    return products_of_posnat_powers.instantiate(
                            {a:same_base, m:_m, k:_k}, assumptions=assumptions)
            else:
                if self.operands.is_binary():
                    _b, _c = operand_exponents
                    if known_exponent_type == RealsPos:
                        thm = product_of_pos_powers
                    elif known_exponent_type == Reals:
                        thm = product_of_real_powers
                    else: # Complex is default
                        thm = product_of_complex_powers
                    return thm.instantiate({a:same_base, b:_b, c:_c},
                                           assumptions=assumptions)                    
                else:
                    _b = ExprTuple(*operand_exponents)
                    _m = _b.length(assumptions)
                    if known_exponent_type == RealsPos:
                        thm = products_of_pos_powers # plural products
                    elif known_exponent_type == Reals:
                        thm = products_of_real_powers # plural products
                    else: # Complex is default
                        thm = products_of_complex_powers 
                    return thm.instantiate({m:_m, a:same_base, b:_b},
                                           assumptions=assumptions)                 
            
        elif same_exponent not in (None, False):
            # Same exponent: equate $a^c b^c = (a b)^c$
            # Combining the exponents in this case is the reverse
            # of disibuting an exponent.
            prod = Mult(*operand_bases)
            exp = Exp(prod, same_exponent)
            return exp.distribution(assumptions).deriveReversed(assumptions)
        raise ValueError('Product is not in a correct form to '
                         'combine exponents: ' + str(self))

    def commutation(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index initIdx has been moved to finalIdx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via initIdx = 1 and finalIdx = -2.
        '''
        from ._theorems_ import commutation, leftwardCommutation, rightwardCommutation
        return apply_commutation_thm(self, initIdx, finalIdx, commutation, leftwardCommutation, rightwardCommutation, assumptions)

    def groupCommutation(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operands
        at indices [initIdx, initIdx+length) have been moved to [finalIdx. finalIdx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return groupCommutation(self, initIdx, finalIdx, length, disassociate, assumptions)

    def association(self, startIdx, length, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which operands in the
        range [startIdx, startIdx+length) are grouped together.
        For example, (a + b + ... + y + z) = (a + b ... + (l + ... + m) + ... + y + z)
        '''
        from ._theorems_ import association
        return apply_association_thm(self, startIdx, length, association, assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) = (a + b + ... + y + z)
        '''
        from ._theorems_ import disassociation
        return apply_disassociation_thm(self, idx, disassociation, assumptions)

# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(Mult, 'commutation', 'commuted', 'commute')
InnerExpr.register_equivalence_method(Mult, 'groupCommutation', 'groupCommuted', 'groupCommute')
InnerExpr.register_equivalence_method(Mult, 'association', 'associated', 'associate')
InnerExpr.register_equivalence_method(Mult, 'disassociation', 'disassociated', 'disassociate')
InnerExpr.register_equivalence_method(Mult, 'distribution', 'distributed', 'distribute')
InnerExpr.register_equivalence_method(Mult, 'factorization', 'factorized', 'factor')
InnerExpr.register_equivalence_method(Mult, 'exponentCombination', 'combinedExponents', 'combineExponents')
