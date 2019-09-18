from proveit import Literal, Operation, Iter, USE_DEFAULTS,StyleOptions, maybeFencedLatex, ProofFailure, InnerExprMethodsObject
from proveit._common_ import a, b, c, l, m, n, x, y, AA, BB, CC, A, B, C, aa, cc, dd
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit.number.numeral.deci import DIGITS
import proveit.number.numeral.deci._theorems_
from proveit.abstract_algebra.inner_expr_mixins import CommutativeAndAssociativeInnerExprMixin, DistributiveInnerExprMixin
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, groupCommutation, pairwiseEvaluation
from proveit import TransRelUpdater
import bisect

class Add(Operation):
    # operator of the Add operation
    _operator_ = Literal(stringFormat='+', context=__file__)
    
    # Map terms to sets of KnownTruth equalities that involve
    # the term on the left hand side. 
    knownEqualities = dict()
    
    # Adding two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    addedNumerals = set()
    
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        # The default style will be to use subtraction notation (relevant where operands are negated).
        # Call 'withSubtractionAt' to alter this default.
        subtractionPositions = [k for k, operand in enumerate(operands) if Add._isNegatedOperand(operand)]
        styles = {'subtractionPositions': ','.join(str(pos) for pos in subtractionPositions)}
        Operation.__init__(self, Add._operator_, operands, styles=styles)
        self.terms = self.operands
        if len(self.terms)==2 and all(term in DIGITS for term in self.terms):
            if self not in Add.addedNumerals:
                try:
                    # for single digit addition, import the theorem that provides the evaluation
                    Add.addedNumerals.add(self)
                    proveit.number.numeral.deci._theorems_.__getattr__('add_%d_%d'%(self.terms[0].asInt(), self.terms[1].asInt()))
                except:
                    # may fail before the relevent _commons_ and _theorems_ have been generated
                    pass # and that's okay
        #assert not isinstance(self.operands[0], Add)
    
    @staticmethod
    def _isNegatedOperand(operand):
        '''
        Returns True iff the given operand is negated directly or an iteration with a negated body
        '''
        from proveit.number import Neg
        return isinstance(operand, Neg) or (isinstance(operand, Iter) and isinstance(operand.lambda_map.body, Neg))

    def styleOptions(self):
        # Added by JML on 9/10/19
        options = StyleOptions(self)
        options.add('subtractionPositions', "Position(s) to use subtraction notation instead of adding the negation at the specified indices")
        return options

    def withSubtractionAt(self, *subtractionPositions):
        return self.withStyles(subtractionPositions='(' + ','.join(str(pos) for pos in subtractionPositions) + ')')

    def subtractionPositions(self):
        '''
        Return a list of subtraction notation positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.getStyle('subtractionPositions').strip('()').split(',') if pos_str != '']


    def _formatted(self, formatType, **kwargs):
        '''
        Override Operation._formatted so to enable subtraction notation where desired.
        '''
        from proveit import Iter
        from proveit.number import Neg
        subtraction_positions = self.subtractionPositions()
        if len(subtraction_positions) > 0 and len(self.operands)>1:
            operators = []
            operands = list(self.operands)
            for operand in operands:
                if isinstance(operand, Iter):
                    # make the operator a Iter in correspondence with the operands Iter
                    operators.append(Iter(operand.lambda_map.parameter_or_parameters, self.operator, operand.start_index_or_indices, operand.end_index_or_indices))
                else:
                    operators.append(self.operator)
            implicitFirstOperator = True # the first operator is implicit if it is a '+'
            for pos in subtraction_positions:
                if pos >= len(operands): continue
                operand = operands[pos]
                if pos==0: implicitFirstOperator=False
                if isinstance(operand, Neg):
                    # format negated operand using subtraction notation
                    operators[pos] = Neg._operator_
                    operands[pos] = operand.operand
                elif isinstance(operand, Iter):
                    if isinstance(operand.lambda_map.body, Neg):
                        # format iteration with negation using subtraction notation
                        operators[pos].body = Iter(operand.lambda_map.parameter_or_parameters, Neg._operator_, operand.start_index_or_indices, operand.end_index_or_indices)
                        operands[pos] = Iter(operand.lambda_map.parameter_or_parameters, operand.lambda_map.body.operand, operand.start_index_or_indices, operand.end_index_or_indices, operand.getStyles())
                elif pos==0: implicitFirstOperator=False # not negated after all -- revert to the "implicit first operator" default
            return Operation._formattedOperation(formatType, operators, operands, self.wrapPositions(), self.getStyle('justification'), implicitFirstOperator=implicitFirstOperator, **kwargs)
        else:
            return Operation._formattedOperation(formatType, self.operator, self.operands, self.wrapPositions(), self.getStyle('justification'), **kwargs)

    def remakeConstructor(self):
        # Added by JML on 9/10/19
        if len(self.operands)==2 and self.subtractionPositions() == (1,) and Add._isNegatedOperand(self.operands[1]):
            return 'subtract'  # use a different constructor if using the subtraction style
        return Operation.remakeConstructor(self)

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        from proveit.number import Neg
        if len(self.operands)==2 and self.subtractionPositions() == (1,) and Add._isNegatedOperand(self.operands[1]):
            yield self.operands[0]
            assert isinstance(self.operands[1], Neg), "The second operand must be negated"
            yield self.operands[1].operand
        else:
            for operand in self.operands:
                yield operand

    def innerExprMethodsObject(self, innerExpr):
        return InnerAddition(innerExpr)

    def _closureTheorem(self, numberSet):
        from ._theorems_ import addNatClosure, addRealClosure, addComplexClosure, addIntClosure
        from proveit.number import Reals, Complexes, Integers, Naturals
        if numberSet == Reals:
            return addRealClosure
        elif numberSet == Complexes:
            return addComplexClosure
        elif numberSet == Integers:
            return addIntClosure
        elif numberSet == Naturals:
            return addNatClosure
    """
    def conclude(selfs, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19
        conclude method for proof automation
        '''
        raise ValueError("conclude currently not implemented for add")
    """
    """
    # An Add should not have side-effects because it cannot
    # be proven.  - wmw.
    def sideEffects(self, knownTruth):
        '''
        side effects for addition
        added by JML on 9/10/19
        '''
        # print("sideEffects")
        from proveit.number import zero
        # print("deriving zero from neg self")
        yield self.deriveZeroFromNegSelf
        if (self.terms[0] == zero or self.terms[1] == zero) and len(self.terms) == 2:
           # print("deducing add zero")
            yield self.deduceAddZero
    """


    def equalitySideEffects(self, knownTruth):
        '''
        Record the knownTruth in Add.knownEqualities, associated for
        each term.
        '''
        #print("equality side Effects on", self)
        from proveit.number import Neg, zero
        if isinstance(self.operands[0], Neg):
            # print("there is a neg:", self)
            return
        if len(self.operands) > 1:
            if isinstance(self.operands[1], Neg):
                # print("there is a neg:", self)
                return
        addition = knownTruth.lhs
        if not isinstance(addition, Add):
            raise ValueError("Expecting lhs of knownTruth to be of an Add expression")
        for term in addition.terms:
            # print("adding known equalities:", term)
            Add.knownEqualities.setdefault(term, set()).add(knownTruth)

        if len(addition.terms)==2:
            # deduce the subtraction form: c-b=a from a+b=c
            # print("deducing subtraction terms:", self)
            yield (lambda assumptions : self.deduceSubtraction(knownTruth.rhs, assumptions))
        

    def deduceStrictIncAdd(self, b, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19. renamed by WMW 9/6/19.

        '''
        from ._theorems_ import strictlyIncreasingAdditions
        from proveit._common_ import m, n, AA, B, CC
        from proveit.number import num
        # print(b)
        for i, term in enumerate(self.terms):
            if term == b:
                idx = i
        nVal = len(self.terms) -1 - idx
        # print(strictlyIncreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx+1:]}, assumptions=assumptions))
        return strictlyIncreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx +1:]}, assumptions=assumptions)

    def deduceStrictDecAdd(self, b, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19. renamed by WMW 9/6/19.

        '''
        from ._theorems_ import strictlyDecreasingAdditions
        from proveit._common_ import m, n, AA, B, CC
        from proveit.number import num
        # print(b)
        # print(self.terms)
        for i, term in enumerate(self.terms):
            if term == b:
                idx = i
        nVal = len(self.terms) -1 - idx
        # print(nVal)
        return strictlyDecreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx +1:]}, assumptions=assumptions)


    def deduceSubtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        # print(self)
        from proveit.number.addition.subtraction._theorems_ import subtractFromAdd
        if len(self.terms) != 2:
            raise Exception("deduceSubtraction implemented only when there are two and only two added terms")
        deduction = subtractFromAdd.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
        # print("deduction", deduction)
        return deduction

    def conversionToMultiplication(self, assumptions=USE_DEFAULTS):
        '''
        From the addition of the same values, derive and return
        the equivalence as a multiplication. For example,
        a + a + a = 3 * a
        '''
        from proveit.number import num
        from proveit.number.multiplication._theorems_ import multDefRev
        if not all(operand==self.operands[0] for operand in self.operands):
            raise ValueError("'asMult' is only applicable on an 'Add' expression if all operands are the same: %s"%str(self))
        return multDefRev.specialize({m:num(len(self.operands)), AA:self.operands, x: self.operands[1]}, assumptions=assumptions)
    
    """
    def deriveExpandedMultDef(self, idx, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/25/19
        given an addition where there is a group of the same values, derive the multiplication
        a + (b + b + b) + c = a + (3 * b) + c
        '''
        from ._theorems_ import expandedMultDef
        from proveit.number import num, Neg
        expr = self
        end = idx + 1
        started = False
        for i, operand in enumerate(expr.operands):
            # loop through all the operands in the grouped idx
            # print("operand", operand)
            # print("expr.operands", expr.operands)

            if i == idx:
                # we have reached the indicated term
                started = True
            if expr.operands[idx] != operand and started:
                # once we reach an operand that is not equal, break
                end = i
                break

        # print("end", end)
        # print("expr, idx", expr, idx)
        # print("l", num(idx))
        # print("m", num(len(expr.operands[idx:end])))
        # print("n", num(len(expr.operands[end+1:])))
        # print("aa", expr.operands[:idx])
        # print("bb", expr.operands[idx:end])
        # print("cc", expr.operands[end + 1:])
        # print("x", expr.operands[idx])
        return expandedMultDef.specialize({l:num(idx),m:num(len(expr.operands[idx:end])), n: num(len(expr.operands[end :])), AA:expr.operands[:idx],BB:expr.operands[idx:end],CC:expr.operands[end :], x:expr.operands[idx]}, assumptions=assumptions)
    """
    def deduceAddZero(self, assumptions=USE_DEFAULTS):
        '''
        added by JML on 7/10/19
        Given x + 0 return x.
        '''
        from ._theorems_ import addZero
        from proveit.number import zero
        if self.terms[1] ==  zero:
            value = 0
        elif self.terms[0] == zero:
            value = 1
        return addZero.specialize({x:self.terms[value]}, assumptions=assumptions)
    
    def cancelations(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        all simple cancellations are performed (where there are exact
        negations that occur).
        '''
        from proveit.number import Neg
        
        expr = self
        
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions) 
        
        neg_operand_indices = dict()
        for i, operand in enumerate(self.operands):
            if isinstance(operand, Neg):
                neg_operand_indices.setdefault(operand.operand, set()).add(i)
        
        canceled_indices = []
        for i, operand in enumerate(self.operands):
            if isinstance(operand, Neg): continue
            if operand in neg_operand_indices:
                j = neg_operand_indices[operand].pop()
                # By finding where i and j will be inserted into the canceled_indices
                # array, we can figure out how much they need to shift by to compensate
                # for previous cancelations.
                i_shift = bisect.bisect_left(canceled_indices, i)
                j_shift = bisect.bisect_left(canceled_indices, j)
                # insert the last one first so we don't need to compensate:
                if i < j:
                    canceled_indices.insert(j_shift, j)
                    canceled_indices.insert(i_shift, i)
                else:
                    canceled_indices.insert(i_shift, i)
                    canceled_indices.insert(j_shift, j)                    
                expr = eq.update(expr.cancelation(i-i_shift, j-j_shift, assumptions))
        return eq.relation
            
    def cancelation(self, i, j, assumptions=USE_DEFAULTS):
        '''
        Attempt a simple cancelation between operands at index i and j.
        If one of these operands is the negation of the other, deduce
        and return an equality between self and a form in which these
        operands are canceled.
        '''
        from .subtraction._theorems_ import addCancelBasic, addCancelReverse, addCancelGeneral, addCancelGeneralRev
        from proveit.number import num, Neg
        if i > j:
            return self.cancelation(j, i, assumptions) # choose i to be less than j
            
        if Neg(self.operands[i]) == self.operands[j]:
            basic_thm = addCancelBasic
            general_thm = addCancelGeneral
            canceled_op = self.operands[i]
        elif self.operands[i] == Neg(self.operands[j]):
            basic_thm = addCancelReverse
            general_thm = addCancelGeneralRev
            canceled_op = self.operands[j]
        else:
            raise ValueError("Unable to cancel operands i and j; one is not the negation of the other.")
        
        if len(self.operands)==2:
            return basic_thm.specialize({a:canceled_op}, assumptions=assumptions)
        else:
            aSub = self.operands[:i]
            bSub = canceled_op
            cSub = self.operands[i+1:j]
            dSub = self.operands[j+1:]
            lSub = num(len(aSub))
            mSub = num(len(cSub))
            nSub = num(len(dSub))
            spec = general_thm.specialize({l:lSub, m:mSub, n:nSub, aa:aSub, b:bSub, cc:cSub, dd:dSub}, assumptions=assumptions)
            # set the proper subtraction styles to match the original
            sub_positions = self.subtractionPositions()
            spec.innerExpr().lhs.withSubtractionAt(*sub_positions)
            update_pos = lambda p : p if p < i else (p-1 if p < j else p-2)
            spec.innerExpr().rhs.withSubtractionAt(*[update_pos(p) for p in sub_positions])
            return spec
    
    def deduceZeroFromNegSelf(self, assumptions=USE_DEFAULTS):
        '''
        added by JML on 9/10/19. renamed by WMW on 9/6/19.
        Given x + (-x) return x.
        '''
        from ._theorems_ import addNegSelf
        from proveit.number import Neg
        if len(self.operands) != 2:
            raise IndexError("Expecting two operands.  Use substitution and innerExpr() for more than two operands")
        if isinstance(self.operands[0], Neg):
            if self.operands[0].operand != self.operands[1]:
                raise ValueError("Expecting one value to be the negation of the other")
        elif isinstance(self.operands[1], Neg):
            if self.operands[0] != self.operands[1].operand:
                raise ValueError("Expecting one value to be the negation of the other")
        else:
            raise ValueError("Expecting at least one value to be negated")
        return addNegSelf.specialize({x:self.terms[0]}, assumptions=assumptions)
    """
    def deriveExpandedNegSelf(self, idx=0, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/26/19
        given an expression with a term that is a negation of itself cancel them out
        a + b + (-b) + c = a + c
        '''
        from ._theorems_ import expandedAddNegSelf
        from proveit.number import Neg, num
        expr = self
        # print("self, idx in addNegSelf", expr, idx)
        if len(expr.operands) ==2:
            # the simple binary case
            return expr.deriveZeroFromNegSelf(assumptions)

        if idx < 0 or idx > len(expr.operands) - 1:
            raise IndexError("Index must be between 0 and %s"%str(len(expr.operands)-1))
        if not isinstance(expr.operands[idx], Neg):
            raise ValueError("Expecting value at %s to be negated"%str(idx))

        if idx != len(expr.operands) - 1 and expr.operands[idx + 1] == expr.operands[idx].operand:
            one = expr.operands[idx].operand
            two = expr.operands[idx + 1]
            oneIdx = idx
            twoIdx = idx + 1
        elif idx != 0 and expr.operands[idx - 1] == expr.operands[idx].operand:
            one = expr.operands[idx - 1]
            two = expr.operands[idx].operand
            oneIdx = idx - 1
            twoIdx = idx
        else:
            raise ValueError("Expecting a value next to %s to be equal to %s"%(str(expr.operands[idx]), str(expr.operands[idx].operand)))

        return expandedAddNegSelf.specialize({m:num(oneIdx),n:num(len(expr.operands)-1-twoIdx), AA:expr.operands[:oneIdx], y:one, x:two, BB:expr.operands[twoIdx + 1:]}, assumptions=assumptions)
    """
    def _createDict(self, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/24/19
        Creates a dictionary from an addition expression where the keys are common terms and values
        are the indices where they occur.  Also returns the order of initial occurrence for each
        type of term.
        JML had, at my (WMW) suggestion, had positive terms come before negative terms.  This was
        working fine but I removed this feature because it isn't clear that it is always desirable
        and may be better to mess with the order minimally.
        '''
        from proveit import Variable
        from proveit.number import one, two, num, Neg, Mult, Numeral
        from proveit import ExprList
        
        hold = {}
        order = []
        
        for i, val in enumerate(self.operands):
            # loop through each operand

            # used to differentiate positive and negative for ordering
            if isinstance(val, Neg):
                # place it in the correct place regardless of negation
                val = val.operand
            elif isinstance(val, Mult):
                # use the last factor to determine what is a "like" term
                val = val.operands[-1]
            if isinstance(val, Numeral) or (isIrreducibleValue(val) and not isinstance(val, Literal)):
                # Group together all basic numbers (numerals, numeral sequences, and decimals),
                # using 1 as a representative.
                # But exclude special number constants like e, i, or pi which are Irreducible Literals.
                # Those should be grouped together.
                val = one

            # either create a new key or put in an existing key
            if val in hold:
                # if the key exists, just add the value to the list
                hold[val].append(i)
            else:
                # if not, create the key and add the value
                hold[val] = [i]
                order.append(val)

        
        # See if we can expand the "terms" to be combined to
        # include more factors.
        for k, val in enumerate(order):
            if val==one: continue
            if isinstance(val, Neg) and val in hold: 
                continue # positive and negatives are handled together when possible
            # start with the most expanded and widdle down as needed
            newval = self.operands[hold[val][0]]
            if isinstance(newval, Neg):
                newval = newval.operand # overlook the negation at the moment
            for i in hold[val][1:]:
                operand = self.operands[i]
                if isinstance(operand, Neg):
                    operand = operand.operand # overlook the negation
                while newval != operand:
                    try:
                        if isinstance(operand, Mult):
                            operand.index(newval)
                            # newval is contained as a factor in the operand, so keep it as is for now.
                            break
                    except ValueError:
                        pass
                    assert isinstance(newval, Mult), "This is unexpected"
                    if len(newval.operands) > 2:                            
                        newval = Mult(newval.operands[1:])
                    else:
                        newval = newval.operands[-1]
            if isinstance(val, Neg):
                newval = Neg(newval) # put the negation back
            if newval != val:
                # replace the "term" with an expanded term
                hold[newval] = hold[val]
                del hold[val]
                order[k] = newval
        
        return hold, order

    """
    def groupLikeTerms(self, assumptions=USE_DEFAULTS):
        '''
        Given an expression, group terms that are similar
        created by JML 7/25/19
        '''
        from proveit.number import Mult
        m = 0
        expr = self
        eq = TransRelUpdater(expr) # for convenience updating our equation
        length = len(expr.operands)
        while m < length:
            # we will cycle through all values in the expression.
            if m + 1 < length:
                # check to see if we have reached the end
                idx = 1
                One = expr.operands[m]
                if isinstance(One, Mult):
                   One = One.operands[1]
                # the first value of a group
                Two = expr.operands[m + idx]
                if isinstance(Two, Mult):
                   Two = Two.operands[1]
                # the last value of a group

                new = False # used to check if Two has changed
                while One == Two or (isinstance(One, Literal) and isinstance(Two, Literal)):
                    # check to see if the current value is equal to the rest of the values
                    # print(One, Two)

                    idx += 1
                    # print("in loop idx, m, length", idx, m, length)
                    # increment the position of the next operand
                    if m + idx < length:
                        # check to see if we have reached the end
                        Two = expr.operands[m + idx]
                        if isinstance(Two, Mult):
                            Two = Two.operands[1]
                        # move on to the next operand
                        new = True
                        # we have moved on to another operand
                    else:
                        # if we have reached the end, stop the loop
                        if not new:
                            idx -=1
                        break
                if new: idx -= 1
                # print("one, two, idx", One,Two,idx)
                # if we incremented at least once, we need to subtract 1 because the last value was not equal
                Two = expr.operands[m + idx]
                if isinstance(Two, Mult):
                    Two = Two.operands[1]
                # redefine two to reflect the end of the group

                if One == Two or (isinstance(One, Literal) and isinstance(Two, Literal)):
                    # as long as the first and last are equal, we assume anything in between is as well because
                    # we checked above. Derive the group from one to two
                    # print("deriving group, expr, m , m+idx", expr, m, m+idx)
                    expr = eq.update(expr.association(m, length=idx+1, assumptions=assumptions))
                    length -= idx
                    # we account for the change in length because of the grouping
            m += 1
            # move on to the next value after the group
        return expr
    """

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/24/19. modified by WMW on 9/7/19.
        combine like terms.
        '''
        from proveit import Variable
        from proveit.number import zero, one, num, Neg, Mult
        from proveit.logic import Equals
        
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        
        # ungroup the expression (disassociate nested multiplications).
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                expr = eq.update(expr.disassociation(n, assumptions))
            length = len(expr.operands)
            n += 1
        
        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        
        # separate the types of operands in a dictionary
        hold, order = expr._createDict(assumptions)
        
        if len(order) > 0:
            # Reorder the terms so like terms.
            pos = 0
            # The indices keep moving as we reorder, so keep on top of this.
            old2new = {k:k for k in range(len(expr.operands))}
            new2old = {k:k for k in range(len(expr.operands))}
            for key in order:
                for orig_idx in hold[key]:
                    start_idx = old2new[orig_idx]
                    if start_idx==pos: 
                        pos += 1
                        continue # no change. move on.
                    expr = eq.update(expr.commutation(start_idx, pos, assumptions=assumptions))
                    old2new[new2old[start_idx]] = pos
                    orig_old_idx = new2old[start_idx]
                    if start_idx < pos:
                        # decrement indices
                        for new_idx in range(start_idx, pos):
                            new2old[new_idx] = new2old[new_idx+1]
                            old2new[new2old[new_idx]] -= 1
                    else:
                        # increment indices
                        for new_idx in range(start_idx, pos, -1):
                            new2old[new_idx] = new2old[new_idx-1]
                            old2new[new2old[new_idx]] += 1
                    new2old[pos] = orig_old_idx
                    pos += 1
            
            # Now group the terms so we can combine them.
            for m, key in enumerate(order):        
                if len(hold[key]) > 1:
                    expr = eq.update(expr.association(m, length=len(hold[key]), assumptions=assumptions))
        
        
        '''
        # combine like terms
        # cancel negated terms if it can be done
        # j acts as a more accurate count of i
        j = 0
        for i, operand in enumerate(expr.operands):
            # loop through all the operands
            if isinstance(operand, Neg):
                # the operand is negated
                # print("expr, operand, j", expr, operand, j)
                if j != len(expr.operands) - 1 and expr.operands[j + 1] == expr.operands[j].operand:
                    # checks to make sure that there is a term after the negated term
                    key = operand
                    if key in hold:
                        if len(hold[operand]) == 1:
                            # if the negated operand is the only value in it's key, delete the key as well.
                            del order[order.index(operand)]
                    key = str(operand.operand)
                    if key in hold:
                        if len(hold[str(operand.operand)]) == 1:
                            # if the operand that will be cancelled is the only value in it's key, delete the key as well.
                            del order[order.index(str(operand.operand))]
                    # print("j", j)
                    expr = expr.association(j, length=2, assumptions=assumptions).rhs
                    # print(702)
                    Equals(self, expr).prove(assumptions)
                    # print(expr)
                    sub = expr.operands[j].deduceZeroFromNegSelf(assumptions)
                    expr = sub.substitution(expr.innerExpr().operands[j], assumptions=assumptions).rhs
                    # print(707)
                    Equals(self, expr).prove(assumptions)
                    # accounts for the change of the length of the expression after the cancellation
                    j -=2
                elif j != 0 and expr.operands[j - 1] == expr.operands[j].operand:
                    # if there is not a term after the negated term, checks to make sure there is one before
                    key = operand
                    if key in hold:
                        if len(hold[key]) == 1:
                            # if the negated operand is the only value in it's key, delete the key as well.
                            del order[order.index(operand)]
                    key = str(operand.operand)
                    if key in hold:
                        if len(hold[key]) == 1:
                            # if the operand that will be cancelled is the only value in it's key, delete the key as well.
                            del order[order.index(str(operand.operand))]
                    # print("j",j)
                    expr = expr.association(j-1, length=2, assumptions=assumptions).rhs
                    # print(725)
                    Equals(self, expr).prove(assumptions)
                    # print(expr)
                    sub = expr.operands[j-1].deduceZeroFromNegSelf(assumptions)
                    expr = sub.substitution(expr.innerExpr().operands[j-1], assumptions=assumptions).rhs
                    # print(730)
                    Equals(self, expr).prove(assumptions)
                    # accounts for the change of the length of the expression after the cancellation
                    j-=1
            # moving on to the next term
            j += 1
        '''

        # print("expr after group like terms", expr)
        # rewrite the dictionary to reflect this change
        #hold,no = expr._createDict(assumptions)
        # print("new dict after group", hold)
        # print("order", order)
        
        if expr==self: 
            # No grouping occurred so all operands are like terms.
            # Simplify by combining them.
            
            # If all the operands are the same, combine via multiplication.
            if all(operand==self.operands[0] for operand in self.operands):
                return self.conversionToMultiplication(assumptions)
            elif key != one:
                # for all the keys that are not basic numbers, derive the multiplication from the addition
                # make sure all the operands in the key are products (multiplication)
                # if it's grouped, send it to become a multiplication
                expr = eq.update(expr.factorization(key, pull="right", assumptions=assumptions))
                sub = expr.operands[0].simplification(assumptions)
                eq.update(sub.substitution(expr.innerExpr().operands[0], assumptions))
                return eq.relation
        """
        # combine like terms by multiplying
        for key in order:
            print(key, expr)
            # loop through all the different types of terms
            # print("key",key)
            if key != "Lit" and key != "LitNeg" :
                # for all the keys that are not literals, derive the multiplication from the addition
                # print("hold[key][0][0]", hold[key][0][0])
                if isinstance(expr.operands[hold[key][0][0]], Add):
                    '''
                    idx = hold[key][0][0]
                    # print(idx)
                    # print(expr.operands[idx].deriveMultDef(assumptions))
                    sub = expr.operands[idx].deriveMultDef(assumptions)
                    # print(expr)
                    # print(expr.innerExpr())
                    # print(expr.innerExpr().operands[idx])
                    # print(sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions))
                    expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).rhs
                    # print("expr before equals",expr)
                    # print(689)
                    Equals(self, expr).prove(assumptions)
                    # rewrite the dictionary to reflect this change
                    hold,no = expr.createDict(assumptions)
                    # print("new dict after mult", hold)
                    # print("order", order)
                    '''
                    idx = hold[key][0][0]
                    # print("idx",idx)
                    # print("operand at idx", expr.operands[idx])
                    # make sure all the operands in the key are products (multiplication)
                    if isinstance(expr.operands[idx], Add):
                        # if it's grouped, send it to become a multiplication
                        sub = expr.operands[idx].createMult(assumptions)
                        # print("sub for mult", sub)
                        expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).lhs
                        # print("new expr after mult", expr)
                        # print(780)
                        Equals(self, expr).prove(assumptions)
                    # print("factor operand at idx", expr.operands[idx].factor(key, assumptions=assumptions))
                    sub = expr.operands[idx].factorization(key, pull="right", assumptions=assumptions)
                    print(expr, "factorization", sub)
                    # print("sub", sub)
                    # print("expr", expr)
                    # print("expr.innerExpr()", expr.innerExpr())
                    # print("expr.innerExpr().operands[idx]", expr.innerExpr().operands[idx])
                    # print("the substitution", sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions))
                    expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).rhs
                    print("now", expr)
                    # print("expr before equals", expr)
                    # print(785)
                    Equals(self, expr).prove(assumptions)
                    # rewrite the dictionary to reflect this change
                    # print("expr.operands[hold[key][0][0]].operands",expr.operands[hold[key][0][0]].operands)
                    hold, no = expr._createDict(assumptions)
                    # print("new dict after mult", hold)
                    # print("order", order)
            else:
                pass
        # print("expr after mult", expr)
        """
        
        '''
        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = expr.deriveUnGroup(n, assumptions).rhs
                # print(804)
                # print(Equals(self, expr).prove(assumptions))
                # print("new expr", expr)
            length = len(expr.operands)
            n += 1
        '''
        
        # simplify the combined terms
        for i, operand in enumerate(expr.operands):
            # print("expr, i, length", expr, i, length)
            if isinstance(operand, Add):
                expr = eq.update(expr.innerExpr().operands[i].simplification(assumptions))
            elif isinstance(operand, Mult):
                if isinstance(operand.operands[0], Add):
                    expr = eq.update(expr.innerExpr().operands[i].operands[0].simplification(assumptions))
                if isinstance(expr.operands[i].operands[0], Add) and len(expr.operands[i].operands[0].operands) == 1:
                    from proveit.number.addition._axioms_ import singleAdd
                    sub = singleAdd.specialize({x:expr.operands[i].operands[0].operands[0]})
                    # print("single Add", sub)
                    expr = eq.update(sub.substitution(expr.innerExpr().operands[i].operands[0], assumptions))

        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = eq.update(expr.disassociation(n, assumptions))
            length = len(expr.operands)
            n += 1
        # print("expr after initial ungroup", expr)
        # print("expr after evaluation", expr)
        # print("last equals!")
        return eq.relation

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/31/19. modified by WMW on 9/7/19.
        evaluate literals in a given expression (used for simplification)
        '''
        from proveit.logic import SimplificationError
        
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        
        # start with cancelations (maybe everything cancels to zero)
        expr = eq.update(self.cancelations(assumptions))
        if isIrreducibleValue(expr):
            return eq.relation
        
        if len(self.operands) > 2:
            expr = eq.update(pairwiseEvaluation(expr, assumptions))
            return eq.relation

        raise SimplificationError("Unable to evaluate %s"%str(self))
        
    def subtractionFolding(self, termIdx=None, assumptions=frozenset()):
        '''
        Given a negated term, termIdx or the first negated term if termIdx is None,
        deduce the equivalence between self and a Subtract form (with the specified
        negated term on the right of the subtraction).  Assumptions
        may be necessary to deduce operands being in the set of Complexes.
        '''
        from proveit.number import Neg
        from proveit.number.addition.subtraction.theorems import addNegAsSubtract
        if termIdx is None:
            for k, term in enumerate(self.terms):
                if isinstance(term, Neg):
                    termIdx = k
                    break
            if termIdx is None:
                raise Exception("No negated term, can't provide the subtraction folding.")
        if not isinstance(self.terms[termIdx], Neg):
            raise ValueError("Specified term is not negated, can't provide the subtraction folding.")
        expr = self
        if termIdx != -1 and termIdx != len(expr.terms)-1:
            # put the negative term at the end
            expr = expr.commute(termIdx, termIdx+1, -1)
        if len(expr.terms) > 2:
            # group all of the other terms
            expr = expr.group(0, -1)
        deduceInComplexes(expr.operands[0], assumptions)
        deduceInComplexes(expr.operands[-1].operand, assumptions)
        return addNegAsSubtract.specialize({x:expr.operands[0], y:expr.operands[-1].operand})
    
    def deduceInNaturalsPosDirectly(self, assumptions=frozenset(), ruledOutSets=frozenset(), dontTryPos=False, dontTryNeg=False):
        '''
        If all of the terms are in Naturals and just one is positive, then the sum is positive.
        '''
        from proveit.number.numberSets import DeduceInNumberSetException, deduceInNaturals, deducePositive
        from ._theorems_ import addNatPosClosure
        from proveit.number import NaturalsPos, Naturals, num
        from proveit._common_  import AA, B, CC, m,n
        # first make sure all the terms are in Naturals
        for term in self.operands:
            deduceInNumberSet(term, assumptions)
        for k, term in enumerate(self.operands):
            #try:
                # found one positive term to make the sum positive
            deducePositive(term, assumptions)
            return addNatPosClosure.specialize({m:num(k), n:num(len(self.operands)-k-1), AA:self.operands[:k], B:term, CC:self.operands[k+1:]}, assumptions=assumptions)
            #except:
               # pass
        # need to have one of the elements positive for the sum to be positive
        raise DeduceInNumberSetException(self, NaturalsPos, assumptions)

    def deduceInNumberSet(self, NumberSet,assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''

        from proveit.number.addition._theorems_ import addIntClosureBin,addIntClosure, addNatClosureBin, addNatClosure, addNatPosClosure, addRealClosureBin, addRealClosure, addComplexClosureBin, addComplexClosure
        from proveit.number import num, Greater, Integers, Naturals, Reals, Complexes, NaturalsPos, zero
        if NumberSet == Integers:
            if len(self.operands) == 2:
                return addIntClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addIntClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if NumberSet == Naturals:
            if len(self.operands) == 2:
                return addNatClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addNatClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if NumberSet == NaturalsPos:
            val = -1
            for i, operand in enumerate(self.operands):
                try:
                    Greater(operand, zero).prove(assumptions=assumptions)
                    val = i
                    # print(b)
                    break
                except ProofFailure:
                    pass
            if val == -1:
                raise ValueError("Expecting at least one value to be greater than zero")
            # print(len(self.operands))
            return addNatPosClosure.specialize({m: num(val), n:num(len(self.operands) - val - 1), AA:self.operands[:val], B: self.operands[val], CC: self.operands[val + 1:]}, assumptions=assumptions)
        if NumberSet == Reals:
            if len(self.operands) == 2:
                return addRealClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addRealClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if NumberSet == Complexes:
            if len(self.operands) == 2:
                return addComplexClosureBin.specialize({a:self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addComplexClosure.specialize({m:num(len(self.operands)), AA: self.operands}, assumptions=assumptions)


    def deduceStrictIncrease(self, lowerBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsPos, deduce an return
        the statement that the sum is greater than the term at lowerBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from ._theorems_ import strictlyIncreasingAdditions
        for i, term in enumerate(self.terms):
            if i == lowerBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsPos(term, assumptions)
        return strictlyIncreasingAdditions.specialize({aEtc:self.terms[:lowerBoundTermIndex], cEtc:self.terms[lowerBoundTermIndex+1:]}).specialize({b:self.terms[lowerBoundTermIndex]}).checked(assumptions)

    def deduceStrictDecrease(self, upperBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsNeg, deduce an return
        the statement that the sum is less than the term at upperBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from ._theorems_ import strictlyDecreasingAdditions
        for i, term in enumerate(self.terms):
            if i == upperBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsNeg(term, assumptions)
        return strictlyDecreasingAdditions.specialize({aEtc:self.terms[:upperBoundTermIndex], cEtc:self.terms[upperBoundTermIndex+1:]}).specialize({b:self.terms[upperBoundTermIndex]}).checked(assumptions)
    
    """
    def createMult(self, assumptions=USE_DEFAULTS):
        '''
        given an expression, turn all the operands into multiplication
        created by JML on 7/31/19
        '''
        from proveit.number.multiplication._theorems_ import distributeThroughSum, multOneLeft
        from proveit.number import num, Mult, one, Neg
        from proveit.logic import Equals
        from proveit import Variable
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        for k, operand in enumerate(expr.operands):
            # loop through all the operands
            # print("expr", expr)
            # print(operand)
            if isinstance(operand, Neg):
                # turn it into -1 * the factor
                from proveit.number.negation._theorems_ import negAsMultOne
                sub = negAsMultOne.specialize({x:operand.operand}, assumptions=assumptions)
                # print("done with sub", sub)
                expr = eq.update(sub.substitution(expr.innerExpr().operands[k], assumptions))
            elif isinstance(operand, Variable):
                # turn it into 1 * the factor
                sub = multOneLeft.specialize({x: expr.operands[k]}, assumptions=assumptions)
                # print("sub", sub)
                # sub = Add(expr.operands[k]).deriveMultDef(assumptions)
                # print(sub)
                # print("substitution", sub.substitution(expr.innerExpr().operands[k], assumptions))
                expr = eq.update(sub.substitution(expr.innerExpr().operands[k], assumptions))
            # print("operand after mult change",operand)
            # print("new expr", expr)
        return eq.relation
    """
        
    """
    def factor(self, theFactor, pull="left", groupFactor=True, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this sum, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, these operands are grouped
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        updated by JML on 7/30/19
        '''
        from proveit.number.multiplication._theorems_ import distributeThroughSum, multOne
        from proveit.number import num, Mult, one, Neg
        from proveit.logic import Equals
        expr = self
        coefficient = []
        after = []
        numberOfFactors = 0

        for operand in expr.operands:
            if not isinstance(operand, Mult):
                expr = expr.createMult(assumptions).rhs
                break

        for k, operand in enumerate(expr.operands):
            # loop through all the operands
            # print("expr", expr)
            # print(operand)
            if isinstance(operand, Mult):
                # print("operand is mult")
                for i, term in enumerate(operand.operands):
                    # print(i, term)
                    # loop through the operands of mult
                    # print("operand.operands[:i}", operand.operands[:i])
                    if term == theFactor:
                        numberOfFactors +=1
                        coefficient.extend(operand.operands[:i])
                        if i + 1 < len(operand.operands):
                            after.extend(operand.operands[i+1:])

        if pull == "right":
            b = coefficient
            a = after
        else:
            b = after
            a = coefficient

        # print("l", num(len(a)))
        # print("m", num(len(b)))
        # print("n", one)
        # print("aa", a)
        # print("bb", b)
        # print("cc",theFactor)
        # print(1045)
        Equals(self, expr).prove(assumptions)
        return distributeThroughSum.specialize({l:num(len(a)),m:num(len(b)),n:one,AA:a,BB:b,CC:[theFactor]}, assumptions=assumptions).deriveReversed(assumptions=assumptions)
    """
            
    def factorization(self, theFactor, pull="left", groupFactor=True, assumptions=USE_DEFAULTS):
        '''
        Factor out "theFactor" from this sum, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, these operands are grouped 
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.logic import Equals
        from proveit.number.multiplication._theorems_ import distributeThroughSum
        from proveit.number import num, one, Mult, Neg
        expr = self
        ySub = []
        # factor theFactor from each term
        for i, term in enumerate(self.terms):
            if hasattr(term, 'factorization'):
                termFactorization = term.factorization(theFactor, pull, groupFactor=groupFactor, groupRemainder=True, assumptions=assumptions)
                if not isinstance(termFactorization.rhs, Mult):
                    raise Exception('Expecting right hand size of factorization to be a product')
                if pull == 'left':
                    # the grouped remainder on the right
                    ySub.append(termFactorization.rhs.operands[-1]) 
                else:
                    # the grouped remainder on the left
                    ySub.append(termFactorization.rhs.operands[0])
            else:
                if term != theFactor:
                    raise ValueError("Factor, %s, is not present in the term at index %d of %s!"%(theFactor, i, self))
                factoredTerm = Mult(one, term) if pull=='right' else Mult(term, one)
                termFactorization = factoredTerm.simplification(assumptions).deriveReversed(assumptions)
                ySub.append(one)
                
            # substitute in the factorized term
            expr = termFactorization.substitution(expr.innerExpr().terms[i], assumptions=assumptions).rhs
            Equals(self, expr).prove(assumptions)
        if not groupFactor and isinstance(theFactor, Mult):
            factorSub = theFactor.operands
        else:
            factorSub = [theFactor]
        if pull == 'left':
            xSub = factorSub
            zSub = []
        else:
            xSub = []
            zSub = factorSub
        expr = distributeThroughSum.specialize({l:num(len(xSub)),m:num(len(ySub)),n:num(len(zSub)),AA:xSub, BB:ySub, CC:zSub}, assumptions=assumptions).deriveReversed(assumptions).rhs
        return Equals(self, expr).prove(assumptions)
    
    """
    # DOES NOT APPEAR TO BE USED
    def join(self, assumptions=frozenset()):
        '''
        For joining two summations (could be more sophisticated later).
        '''
        from proveit.number import Sum
        if len(self.terms) != 2 or not all(isinstance(term, Sum) for term in self.terms):
            raise Exception("Sum joining currently only implemented for two summation terms.")
        return self.terms[0].join(self.terms[1], assumptions)
    """
    

    def commutation(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index initIdx has been moved to finalIdx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via initIdx = 1 and finalIdx = -2.
        '''
        from ._theorems_ import commutation, leftwardCommutation, rightwardCommutation
        eq = apply_commutation_thm(self, initIdx, finalIdx, commutation, leftwardCommutation, rightwardCommutation, assumptions)
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.
        
        # set the subraction style as appropriate:
        subtraction_positions = self.subtractionPositions()
        eq.innerExpr().lhs.withSubtractionAt(*subtraction_positions)
        
        eq.innerExpr().rhs.withSubtractionAt(*)
        '''
        return eq
        

    def groupCommutation(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operands
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
        eq = apply_association_thm(self, startIdx, length, association, assumptions)
        
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.
        # set the subraction style as appropriate given what we started with:
        subtraction_positions = self.subtractionPositions()
        eq.innerExpr().lhs.withSubtractionAt(*subtraction_positions)
        beg_positions = [p for p in subtraction_positions if p < startIdx]
        inner_positions = [p-startIdx for p in subtraction_positions if startIdx <= p < startIdx+length]
        end_positions = [p-length for p in subtraction_positions if p > startIdx+length]
        eq.innerExpr().rhs.operands[startIdx].withSubtractionAt(*inner_positions)
        eq.innerExpr().rhs.operands[startIdx].withSubtractionAt(*(beg_positions + end_positions))
        '''
        return eq

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) = (a + b + ... + y + z)
        '''
        from ._theorems_ import disassociation
        eq = apply_disassociation_thm(self, idx, disassociation, assumptions)
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.
        # set the subraction style as appropriate given what we started with:
        subtraction_positions = self.subtractionPositions()
        inner_positions = self.operand[idx].subtractionPositions()
        inner_num_operands = len(self.operand[idx])
        eq.innerExpr().lhs.operands[idx].withSubtractionAt(*inner_positions)
        eq.innerExpr().lhs.withSubtractionAt(*subtraction_positions)
        new_positions = [p for p in subtraction_positions if p < idx]
        new_positions.extend([p+idx for p in inner_positions])
        new_positions.extend([p+inner_num_operands for p in subtraction_positions if p > idx])
        eq.innerExpr().rhs.withSubtractionAt(*new_positions)
        '''
        return eq

def subtract(a, b):
    from proveit.number import Neg
    if isinstance(b, Iter):
        b = Iter(b.lambda_map.parameter_or_parameters, Neg(b.lambda_map.body), b.start_index_or_indices, b.end_index_or_indices, b.getStyles())
        return Add(a, b).withSubtractionAt(1) # this style is the default, but just to be clear.
    return Add(a, Neg(b)).withSubtractionAt(1) # this style is the default, but just to be clear.

class InnerAddition(DistributiveInnerExprMixin, CommutativeAndAssociativeInnerExprMixin, InnerExprMethodsObject):
    def __init__(self, innerExpr):
        InnerExprMethodsObject.__init__(self, innerExpr)
        if not isinstance(self.expr, Add):
            raise TypeError("InnerAddition is expecting an Add object as the inner expression")
