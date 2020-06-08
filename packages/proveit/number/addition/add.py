from proveit import KnownTruth, Literal, Operation, Iter, USE_DEFAULTS,StyleOptions, maybeFencedLatex, ProofFailure, InnerExpr
from proveit._common_ import a, b, c, l, m, n, x, y, AA, BB, CC, A, B, C, aa, bb, cc, dd
from proveit.logic import Equals
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit.number.numeral.deci import DIGITS
import proveit.number.numeral.deci._theorems_
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
        from proveit.number import Neg
        # The default style will be to use subtraction notation (relevant where operands are negated).
        # Call 'withSubtractionAt' to alter this default.
        subtractionPositions = [k for k, operand in enumerate(operands) if Add._isNegatedOperand(operand)]
        styles = {'subtractionPositions': '(' + ' '.join(str(pos) for pos in subtractionPositions) +')'}
        Operation.__init__(self, Add._operator_, operands, styles=styles)
        self.terms = self.operands
    
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
        return self.withStyles(subtractionPositions='(' + ' '.join(str(pos) for pos in subtractionPositions) + ')')

    def subtractionPositions(self):
        '''
        Return a list of subtraction notation positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.getStyle('subtractionPositions').strip('()').split(' ') if pos_str != '']


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

    def remakeWithStyleCalls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a 
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'withWrappingAt'
        and 'withJustification' calls.
        '''
        call_strs = Operation.remakeWithStyleCalls(self)
        subtraction_positions = self.subtractionPositions()
        default_subtraction_positions = [k for k, operand in enumerate(self.operands) if Add._isNegatedOperand(operand)]
        if subtraction_positions != default_subtraction_positions:
            call_strs.append('withSubtractionAt(' + ','.join(str(pos) for pos in subtraction_positions) + ')')
        return call_strs    

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

    def equalitySideEffects(self, knownTruth):
        '''
        Record the knownTruth in Add.knownEqualities, associated for
        each term.
        '''
        from proveit.number import Neg
        if not isinstance(knownTruth, KnownTruth):
            raise ValueError("Expecting 'knownTruth' to be a KnownTruth.")
        if not isinstance(knownTruth.expr, Equals):
            raise ValueError("Expecting the knownTruth to be an equality.")
        addition = knownTruth.lhs
        if not isinstance(addition, Add):
            raise ValueError("Expecting lhs of knownTruth to be of an Add expression.")
        
        if isIrreducibleValue(knownTruth.rhs):
            for term in addition.terms:
                # print("adding known equalities:", term)
                Add.knownEqualities.setdefault(term, set()).add(knownTruth)
            
            if len(addition.terms)==2:
                # deduce the commutation form: b+a=c from a+b=c
                if addition.terms[0] != addition.terms[1]:
                    yield (lambda assumptions : knownTruth.innerExpr().lhs.commute(0, 1, assumptions))
    
                if all(not isinstance(term, Neg) for term in addition.terms):
                    # From a+b=c
                    # deduce the negations form: -a-b=-c
                    #      the subtraction form: c-b=a
                    #      and the reversed subtraction form: b-c = -a
                    yield (lambda assumptions : self.deduceNegation(knownTruth.rhs, assumptions))            
                    yield (lambda assumptions : self.deduceSubtraction(knownTruth.rhs, assumptions))            
                    yield (lambda assumptions : self.deduceReversedSubtraction(knownTruth.rhs, assumptions))            

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

    def deduceNegation(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return -(a-b) = -rhs
        '''
        from proveit.number.addition.subtraction._theorems_ import negatedAdd
        if len(self.terms) != 2:
            raise Exception("deduceNegation implemented only when there are two and only two added terms")
        deduction = negatedAdd.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
        return deduction
        
    def deduceSubtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        from proveit.number.addition.subtraction._theorems_ import subtractFromAdd
        if len(self.terms) != 2:
            raise Exception("deduceSubtraction implemented only when there are two and only two added terms")
        deduction = subtractFromAdd.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
        return deduction

    def deduceReversedSubtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return b - rhs = -a.
        '''
        from proveit.number.addition.subtraction._theorems_ import subtractFromAddReversed
        if len(self.terms) != 2:
            raise Exception("subtractFromAddReversed implemented only when there are two and only two added terms")
        deduction = subtractFromAddReversed.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
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
        from .subtraction._theorems_ import addCancelTriple_12, addCancelTriple_13, addCancelTriple_23
        from .subtraction._theorems_ import addCancelTriple_21, addCancelTriple_31, addCancelTriple_32
        from proveit.number import num, Neg
        if i > j:
            return self.cancelation(j, i, assumptions) # choose i to be less than j
            
        if Neg(self.operands[i]) == self.operands[j]:
            basic_thm = addCancelBasic
            triple_thms = (addCancelTriple_12, addCancelTriple_13, addCancelTriple_23)
            general_thm = addCancelGeneral
            canceled_op = self.operands[i]
        elif self.operands[i] == Neg(self.operands[j]):
            basic_thm = addCancelReverse
            triple_thms = (addCancelTriple_21, addCancelTriple_31, addCancelTriple_32)
            general_thm = addCancelGeneralRev
            canceled_op = self.operands[j]
        else:
            raise ValueError("Unable to cancel operands i and j; one is not the negation of the other.")
        
        if len(self.operands)==2:
            return basic_thm.specialize({a:canceled_op}, assumptions=assumptions)
        elif len(self.operands)==3:
            # k is the 3rd index, completing i and j in the set {0,1,2}.
            k = {0,1,2}.difference([i, j]).pop()
            thm = triple_thms[2-k]
            return thm.specialize({a:canceled_op, b:self.operands[k]}, 
                                   assumptions=assumptions)
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
    
    def zeroEliminations(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return this Add expression equal to a form in which
        all zero's are eliminated.
        '''
        from proveit.number import zero
        
        expr = self
        
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands)):
            if operand==zero:
                idx = len(self.operands) - rev_idx - 1
                expr = eq.update(expr.zeroElimination(idx, assumptions))
                if not isinstance(expr, Add):
                    break # can't do an elimination if reduced to a single term.
        
        return eq.relation                
    
    def zeroElimination(self, idx, assumptions=USE_DEFAULTS):
        '''
        Derive and return this Add expression equal to a form in which
        a specific zero operand (at the given index) is eliminated.
        '''
        from proveit.number import zero, num
        from ._theorems_ import elimZeroLeft, elimZeroRight, elimZeroAny
        
        if self.operands[idx] != zero:
            raise ValueError("Operand at the index %d expected to be zero for %s"%(idx, str(self)))
        
        if len(self.operands)==2:
            if idx==0:
                return elimZeroLeft.specialize({a:self.operands[1]}, assumptions=assumptions)
            else:
                return elimZeroRight.specialize({a:self.operands[0]}, assumptions=assumptions)
        aVal = self.operands[:idx]
        bVal = self.operands[idx+1:]
        lVal = num(len(aVal))
        mVal = num(len(bVal))
        return elimZeroAny.specialize({l:lVal, m:mVal, aa:aVal, bb:bVal}, assumptions=assumptions)
    
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
        from proveit import ExprTuple
        
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
        
        # ungroup the expression (disassociate nested additions).
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

        # eliminate zeros where possible
        expr = eq.update(expr.zeroEliminations(assumptions))
        if not isinstance(expr, Add):
            # eliminated all but one term
            return eq.relation
                
        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        if not isinstance(expr, Add):
            # canceled all but one term
            return eq.relation
        
        # separate the types of operands in a dictionary
        hold, order = expr._createDict(assumptions)
        
        # Have the basic numbers come at the end.
        if order[-1] != one and one in hold:
            order.pop(order.index(one))
            order.append(one)
        
        if len(order) > 0:
            # Reorder the terms so like terms are adjacent.
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
                
        if expr==self and len(order)==1:
            # All operands are like terms.  Simplify by combining them.
            
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
    
    def _integerBinaryEval(self):
        '''
        Evaluate the sum of possibly negated single digit numbers.
        '''
        from proveit.number import Neg, isLiteralInt, num
        abs_terms = [term.operand if isinstance(term, Neg) else term for term in self.terms]
        if len(abs_terms)!=2 or not all(isLiteralInt(abs_term) for abs_term in abs_terms):
            raise ValueError("_integerBinaryEval only applicable for binary addition of integers")
        a, b = self.terms
        a, b = a.asInt(), b.asInt()
        if a<0 and b<0:
            # evaluate -a-b via a+b
            a, b = -a, -b
        if a<0:
            # evaluate -a+b via (a-b)+b or (b-a)+a
            a=-a
            if a>b:
                a, b = a-b, b
            else:
                a, b = b-a, a
        elif b<0:
            # evaluate a-b via (a-b)+b or (b-a)+a
            b=-b
            if a>b: 
                a, b = a-b, b
            else:
                a, b = b-a, a
        assert a>=0 and b>=0
        #print(a, b)
        if not all(term in DIGITS for term in (num(a), num(b))):
            raise NotImplementedError("Currently, _integerBinaryEval only works for single digit addition and related subtractions: %d, %d"%(a, b))
        if (a, b) not in Add.addedNumerals:
            try:
                # for single digit addition, import the theorem that provides the evaluation
                Add.addedNumerals.add((a, b))
                theorem = proveit.number.numeral.deci._theorems_.__getattr__('add_%d_%d'%(a, b))
                #print(theorem)
            except:
                # may fail before the relevent _commons_ and _theorems_ have been generated
                pass # and that's okay
        # Should have an evaluation now.
        if self not in Equals.known_evaluation_sets:
            raise Exception("Should have an evaluation for %s now.  Why not?  "
                              "Perhaps we were not able to prove that the involved numbers "
                              "are in the Complexes set."%self)
        return self.evaluation() 
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/31/19. modified by WMW on 9/7/19.
        evaluate literals in a given expression (used for simplification)
        '''
        from proveit.logic import SimplificationError
        from proveit.number import Neg, isLiteralInt

        abs_terms = [term.operand if isinstance(term, Neg) else term for term in self.terms]
        if len(abs_terms)==2 and all(isLiteralInt(abs_term) for abs_term in abs_terms):
            # Change the default assumptions will not be necessary after we handle multiple
            # digits properly.  But for now, we need to assume things like "10 in Naturals"
            # and derive side effects under such assumptions.
            from proveit import defaults
            prev_default_assumptions = list(defaults.assumptions)
            defaults.assumptions = assumptions
            evaluation = self._integerBinaryEval()
            defaults.assumptions = prev_default_assumptions # revert back
            return evaluation
        #assert not isinstance(self.operands[0], Add)
                
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        
        # start with cancelations (maybe everything cancels to zero)
        expr = eq.update(self.cancelations(assumptions))
        if isIrreducibleValue(expr):
            return eq.relation
        
        if not isinstance(expr, Add):
            raise SimplificationError("%s simplified to %s which is not irreducible"%(self, expr)) 

        # If all the operands are the same, combine via multiplication and then evaluate.
        if all(operand==expr.operands[0] for operand in expr.operands):
            expr = eq.update(self.conversionToMultiplication(assumptions))
            eq.update(expr.evaluation(assumptions))
            return eq.relation 
        
        if len(expr.operands) > 2:
            expr = eq.update(pairwiseEvaluation(expr, assumptions))
            return eq.relation
        
        if len(self.operands)==2:
            # If both operands are negated, factor out the negation.
            if all(isinstance(operand, Neg) for operand in self.operands):
                negated = Neg(Add(*[operand.operand for operand in self.operands]))
                neg_distribution = negated.distribution(assumptions)
                expr = eq.update(neg_distribution.deriveReversed())
                eq.update(expr.evaluation(assumptions))
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

    def deduceInNumberSet(self, number_set,assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''

        from proveit.number.addition._theorems_ import addIntClosureBin,addIntClosure, addNatClosureBin, addNatClosure, addNatPosClosure, addRealClosureBin, addRealClosure, addComplexClosureBin, addComplexClosure
        from proveit.number import num, Greater, Integers, Naturals, Reals, Complexes, NaturalsPos, zero
        from proveit.logic import InSet
        if number_set == Integers:
            if len(self.operands) == 2:
                return addIntClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addIntClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if number_set == Naturals:
            if len(self.operands) == 2:
                return addNatClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addNatClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if number_set == NaturalsPos:
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
        if number_set == Reals:
            if len(self.operands) == 2:
                return addRealClosureBin.specialize({a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addRealClosure.specialize({m: num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        if number_set == Complexes:
            if len(self.operands) == 2:
                return addComplexClosureBin.specialize({a:self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return addComplexClosure.specialize({m:num(len(self.operands)), AA: self.operands}, assumptions=assumptions)
        msg = "'deduceInNumberSet' not implemented for the %s set"%str(number_set)
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
    
    def deduceDifferenceInNaturals(self, assumptions=USE_DEFAULTS):
        from proveit.number import Neg
        from proveit.number.sets.integer._theorems_ import differenceInNaturals
        if len(self.terms) != 2:
            raise ValueError("deduceDifferenceInNaturals only applicable "
                               "when there are two terms, got %s"%self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError("deduceDifferenceInNaturals only applicable "
                               "for a subtraction, got %s"%self)
        thm = differenceInNaturals
        return thm.specialize({a:self.terms[0], b:self.terms[1].operand},
                               assumptions=assumptions)
        

    def deduceDifferenceInNaturalsPos(self, assumptions=USE_DEFAULTS):
        from proveit.number import Neg
        from proveit.number.sets.integer._theorems_ import differenceInNaturalsPos
        if len(self.terms) != 2:
            raise ValueError("deduceDifferenceInNaturalsPos only applicable "
                               "when there are two terms, got %s"%self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError("deduceDifferenceInNaturalsPos only applicable "
                               "for a subtraction, got %s"%self)
        thm = differenceInNaturalsPos
        return thm.specialize({a:self.terms[0], b:self.terms[1].operand},
                               assumptions=assumptions)
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
            return termFactorization.substitution(expr.innerExpr().terms[i], assumptions=assumptions)
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
        return distributeThroughSum.specialize({l:num(len(xSub)),m:num(len(ySub)),n:num(len(zSub)),AA:xSub, BB:ySub, CC:zSub}, assumptions=assumptions).deriveReversed(assumptions)
    
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
    '''
    Return the a-b expression (which is internally a+(-b)).
    '''
    from proveit.number import Neg
    if isinstance(b, Iter):
        b = Iter(b.lambda_map.parameter_or_parameters, 
                 Neg(b.lambda_map.body), b.start_index_or_indices, 
                 b.end_index_or_indices, b.getStyles())
        # The default style will use subtractions where appropriate.
        return Add(a, b)
    return Add(a, Neg(b))

def dist_subtract(a, b):
    '''
    Returns the distributed a-b expression.  That is, if a or b are
    Add expressions, combine all of the terms into a single Add 
    expression (not nested).  For example, with
    a:x-y, b:c+d-e+g, it would return x-y-c-d+e-g.
    '''
    from proveit.number import Neg
    if isinstance(b, Add):
        bterms = [term.operand if isinstance(term, Neg) else Neg(term) \
                  for term in b.terms]
    elif isinstance(b, Iter):
        bterms = [Iter(b.lambda_map.parameter_or_parameters, 
                       Neg(b.lambda_map.body), b.start_index_or_indices,
                       b.end_index_or_indices, b.getStyles())]
    else:
        bterms = [Neg(b)]
    if isinstance(a, Add):
        aterms = a.terms
    else:
        aterms = [a]
    # The default style will use subtractions where appropriate.
    return Add(*(aterms+bterms)) 

def dist_add(*terms):
    '''
    Returns the distributed sum of expression.  That is, if any of
    the terms are Add expressions, expand them.  For example,
    dist_add(x-y, c+d-e+g) would return x-y+c+d-e+g.
    '''
    from proveit.number import Neg
    expanded_terms = []
    for term in terms:
        if isinstance(term, Add):
            expanded_terms.extend(term.terms)
        else:
            expanded_terms.append(term)
    return Add(*expanded_terms) 


# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(Add, 'commutation', 'commuted', 'commute')
InnerExpr.register_equivalence_method(Add, 'groupCommutation', 'groupCommuted', 'groupCommute')
InnerExpr.register_equivalence_method(Add, 'association', 'associated', 'associate')
InnerExpr.register_equivalence_method(Add, 'disassociation', 'disassociated', 'disassociate')
InnerExpr.register_equivalence_method(Add, 'factorization', 'factorized', 'factor')
InnerExpr.register_equivalence_method(Add, 'cancelation', 'canceled', 'cancel')
InnerExpr.register_equivalence_method(Add, 'cancelations', 'allCanceled', 'allCancel')
InnerExpr.register_equivalence_method(Add, 'zeroElimination', 'eliminatedZero', 'eliminateZero')
InnerExpr.register_equivalence_method(Add, 'zeroEliminations', 'eliminatedZeros', 'eliminateZeros')
