from proveit import Literal, Operation, USE_DEFAULTS,StyleOptions, maybeFencedLatex, ProofFailure, InnerExprMethodsObject
from proveit._common_ import a, b, c, l, m, n, x, y, AA, BB, CC, A, B, C
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit.number.numeral.deci import DIGITS
import proveit.number.numeral.deci._theorems_
from proveit.abstract_algebra.inner_expr_mixins import CommutativeAndAssociativeInnerExprMixin, DistributiveInnerExprMixin
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, groupCommutation, successiveEvaluation

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
        Operation.__init__(self, Add._operator_, operands, styles={'addition': 'Add'})
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

    def styleOptions(self):
        # Added by JML on 9/10/19
        options = StyleOptions(self)
        options.add('addition', "'Subtract': uses '-'; 'Add': uses + ")
        return options

    def string(self, **kwargs):
        from proveit import Iter
        outStr = ''

        if self.getStyle('addition') == 'Subtract':
            # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
            outStr += str(self.operands[0]) + ' - ' + self.operands[1].operand.string(fence=True)
            return outStr
        else:
            return Operation.string(self, **kwargs) # normal addition

    def latex(self, **kwargs):
        # Added by JML on 9/10/19
        if self.getStyle('addition') == 'Subtract':
            # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
            return self.operands[0].latex() + '-' +self.operands[1].operand.latex(fence=True)
        else:
            return Operation.latex(self,**kwargs) # normal addition

    def remakeConstructor(self):
        # Added by JML on 9/10/19
        if self.getStyle('addition') == 'Subtract':
            return 'Subtract'  # use a different constructor if using the subtraction style
        return Operation.remakeConstructor(self)

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        from proveit.number import Neg
        if self.getStyle('addition') == 'Subtract':
            assert len(self.operands) == 2, "Subtract only implemented for the binary case"
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

    def deduceMultDef(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/25/19.  renamed by WMW on 9/6/19.
        Given the addition of the same values, derive the multiplication
        a + a + a = 3 * a
        '''
        from proveit.number import num, Mult

        for operand in self.operands:
            if self.operands[0] != operand:
                raise ValueError("Expecting inputs to be equal to each other.")
        return Mult(num(len(self.operands)), self.operands[0]).deduceMultDef(self, assumptions)
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

    def groupLikeTerms(self, assumptions=USE_DEFAULTS):
        '''
        Given an expression, group terms that are similar
        created by JML 7/25/19
        '''
        from proveit.number import Mult
        m = 0
        expr = self
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
                    expr = expr.association(m, length=idx+1, assumptions=assumptions).rhs
                    length -= idx
                    # we account for the change in length because of the grouping
            m += 1
            # move on to the next value after the group
        return expr

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/24/19. modified by WMW on 9/7/19.
        combine like terms.
        '''
        from proveit import Variable
        from proveit.number import zero, one, Neg, Mult
        from proveit.logic import Equals
        
        expr = self
        # ungroup the expression (disassociate nested multiplications).
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = expr.disassociation(n, assumptions).rhs
                # print(550)
                Equals(self, expr).prove(assumptions)
                # print("new expr", expr)
            length = len(expr.operands)
            n += 1
        
        # print("expr after initial ungroup",expr)
        # separate the types of operands in a dictionary
        hold, firstOrder = expr._createDict(assumptions)
        order = firstOrder
        # print("order", order)
        # Reorder the terms so like terms are together
        for j, key in enumerate(order):
            # loop through all the keys (literals, and any variable keys)
            # print("before loop",hold[key], key)
            size = len(hold[key])
            for l, item in enumerate(hold[key]):
                place = l
                # loop through all the values in each key
                # print("in loop, place, item, size (place < size)", place, item, size-1)
                if place < size:
                    # ensures that we cycle through all of the values for each key despite the changing length of
                    # each key because of grouping.
                    if place != len(hold[key]) - 1:
                        # this if statement ensures that we don't go out of the range of values for each key
                        # print("before if", hold[key][place][0], hold[key][place+1][0] - 1)
                        if hold[key][place] != hold[key][place+1] - 1:
                            # if the index of the first item in the values is not one less than the index of the second value,
                            # then they are not next to each other in the expression.
                            
                            '''
                            # should have already been "ungrouped"
                            for term in expr.operands:
                                # loop through all the operands
                                if isinstance(term, Add):
                                    val = term.operands[0]
                                    if isinstance(val, Neg):
                                        val = term.operands[0].operand
                                    if (val == key or (key == "Lit" and isinstance(val, Literal))):
                                        # if something is grouped and it is the same type as the current key, we assume
                                        # that the original place has been put into the group or it is the first value
                                        place = 0
                            '''

                            # Commute the second value with whatever is next to the first item.
                            # print("place", place)
                            # print("in if", hold[key][place][0], hold[key][place+1][0])
                            # print("swap values",hold[key][place+1][0],hold[key][place][0]+1)
                            # print(expr.commutation(hold[key][place + 1][0], hold[key][place][0] + 1,
                              #                           assumptions=assumptions))
                            if hold[key][place + 1] < hold[key][place] + 1:
                                expr = expr.commutation(hold[key][place + 1], hold[key][place], assumptions=assumptions).rhs
                            elif hold[key][place + 1] > hold[key][place] + 1:
                                expr = expr.commutation(hold[key][place + 1], hold[key][place],
                                                              assumptions=assumptions).lhs
                            # print(603, expr)
                            Equals(self, expr).prove(assumptions)
                            # rewrite the dictionary to reflect this change
                            hold, no = expr._createDict(assumptions)
                            # print("new dict after swap", hold)
                    elif j + 1 < len(order) and hold[order[j]][len(hold[order[j]])-1] + 1 != hold[order[j + 1]][0]:
                        # make sure that the next term is right next to the previous one.
                        # print("j", j)
                        # print("order[j]", order[j])
                        # print("hold", hold)
                        # print("in else", hold[order[j]][len(hold[order[j]])-1][0], hold[order[j + 1]][0][0])
                        # print("swap values", hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1)
                        # print(expr.deriveCommutation(hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1,
                          #                           assumptions=assumptions))
                        if hold[order[j + 1]][0] < hold[order[j]][-1] + 1:
                            expr = expr.commutation(hold[order[j + 1]][0] , hold[order[j]][-1],
                                                          assumptions=assumptions).rhs
                           # print("rhs")
                        if hold[order[j + 1]][0] > hold[order[j]][-1] + 1:
                            expr = expr.commutation(hold[order[j + 1]][0] , hold[order[j]][-1],
                                                          assumptions=assumptions).lhs
                            # print("lhs")
                        # print(603, expr)
                        Equals(self, expr).prove(assumptions)
                        # rewrite the dictionary to reflect this change
                        hold, no = expr._createDict(assumptions)
                        # print("new dict after swap", hold)
                        break
                # print("looping again", l, hold[key])

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

        # group the terms so we can easily combine them
        expr = expr.groupLikeTerms(assumptions)
        # print(739)
        Equals(self, expr).prove(assumptions)
        # print("expr after group like terms", expr)
        # rewrite the dictionary to reflect this change
        #hold,no = expr._createDict(assumptions)
        # print("new dict after group", hold)
        # print("order", order)
        
        if expr==self: 
            # No grouping occurred so all operands are like terms.
            # Simplify by combining them.
            if key != "Lit" and key != "LitNeg" :
                # for all the keys that are not literals, derive the multiplication from the addition
                # make sure all the operands in the key are products (multiplication)
                # if it's grouped, send it to become a multiplication
                expr = expr.createMult(assumptions).lhs
                Equals(self, expr).prove(assumptions)
                expr = expr.factorization(key, pull="right", assumptions=assumptions).rhs
                sub = expr.operands[0].simplification(assumptions)
                expr = sub.substitution(expr.innerExpr().operands[0], assumptions).rhs
                return Equals(self, expr).prove(assumptions)
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
                expr = expr.innerExpr().operands[i].simplification(assumptions).rhs
            elif isinstance(operand, Mult):
                if isinstance(operand.operands[0], Add):
                    expr = expr.innerExpr().operands[i].operands[0].simplification(assumptions).rhs
                if isinstance(expr.operands[i].operands[0], Add) and len(expr.operands[i].operands[0].operands) == 1:
                    from proveit.number.addition._axioms_ import singleAdd
                    sub = singleAdd.specialize({x:expr.operands[i].operands[0].operands[0]})
                    # print("single Add", sub)
                    expr = sub.substitution(expr.innerExpr().operands[i].operands[0], assumptions).rhs
                    # print("after single Add", expr)
                    Equals(self,expr).prove(assumptions)

        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = expr.disassociation(n, assumptions).rhs
                # print(844)
                Equals(self, expr).prove(assumptions)
                # print("new expr", expr)
            length = len(expr.operands)
            n += 1
        # print("expr after initial ungroup", expr)
        # print("expr after evaluation", expr)
        # print("last equals!")
        return Equals(self,expr).prove(assumptions)

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/31/19. modified by WMW on 9/7/19.
        evaluate literals in a given expression (used for simplification)
        '''
        from proveit.logic import Equals, SimplificationError
        from proveit.number import Neg
        
        if len(self.operands)==2 and self.operands[1] == Neg(self.operands[0]):
            # Handle the special case: x-x = 0
            return self.deduceZeroFromNegSelf()
        
        if len(self.operands) > 2:
            return successiveEvaluation(self, assumptions)

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
        for k, operand in enumerate(expr.operands):
            # loop through all the operands
            # print("expr", expr)
            # print(operand)
            if isinstance(operand, Neg):
                # turn it into 1 * the factor
                from proveit.number.negation._axioms_ import negMultOneDef
                # print(negMultOneDef.specialize({x:operand.operand}, assumptions=assumptions))
                sub = negMultOneDef.specialize({x:operand.operand}, assumptions=assumptions)
                # print("done with sub", sub)
                expr = sub.substitution(expr.innerExpr().operands[k], assumptions).rhs
                # print("did expr", expr)
                # print(1045)
                Equals(self, expr).prove(assumptions)
                operand = expr.operands[k]
            elif isinstance(operand, Variable):
                # turn it into 1 * the factor
                sub = multOneLeft.specialize({x: expr.operands[k]}, assumptions=assumptions)
                # print("sub", sub)
                # sub = Add(expr.operands[k]).deriveMultDef(assumptions)
                # print(sub)
                # print("substitution", sub.substitution(expr.innerExpr().operands[k], assumptions))
                expr = sub.substitution(expr.innerExpr().operands[k], assumptions).lhs
                # print(1058)
                Equals(self, expr).prove(assumptions)
                operand = expr.operands[k]
            # print("operand after mult change",operand)
            # print("new expr", expr)
        return Equals(self, expr).prove(assumptions)
        
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
    
    def factorization(self, theFactor, pull="left", groupFactor=True, assumptions=frozenset()):
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
        return apply_commutation_thm(self, initIdx, finalIdx, commutation, leftwardCommutation, rightwardCommutation, assumptions)

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
        return apply_association_thm(self, startIdx, length, association, assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) = (a + b + ... + y + z)
        '''
        from ._theorems_ import disassociation
        return apply_disassociation_thm(self, idx, disassociation, assumptions)



#class Subtract(Operation):

"""
    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Reals:
            return subtraction._theorems_.subtractRealClosure
        elif numberSet == Complexes:
            return theorems.subtractComplexClosure
        elif numberSet == Integers:
            return theorems.subtractIntClosure
        elif numberSet == Naturals:
            return theorems.subtractClosureNats
        elif numberSet == NaturalsPos:
            return theorems.subtractClosureNatsPos

    def _notEqZeroTheorem(self):
        from .theorems import diffNotEqZero
        # Can derive (a - b) != 0 given a != b.
        # Derive a != b from b != a in case we have proven b != a instead of a != b.
        NotEquals(self.operands[1], self.operands[0]).deriveReversed()
        return diffNotEqZero

    def equalitySideEffects(self, knownTruth):
        '''
        Record the knownTruth in Subtract.knownEqualities, associated for
        each term.
        '''
        subtraction = knownTruth.lhs
        if not isinstance(subtraction, Subtract):
            raise ValueError("Expecting lhs of knownTruth to be of an Subtract expression")
        for operand in self.operands:
            Subtract.knownEqualities.setdefault(operand, set()).add(knownTruth)
        # deduce the addition form: c+a=b from a-b=c
        yield (lambda assumptions: self.deduceAddition(knownTruth.rhs, assumptions))

    def deduceAddition(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a - b) = rhs, derive and return rhs + b = a.
        '''
        from proveit.number.addition.subtraction._theorems_ import addFromSubtract
        deduction = addFromSubtract.specialize({a: self.operands[0], b: self.operands[1], c: rhs},
                                               assumptions=assumptions)
        return deduction

    def factor(self, theFactor, pull='left', groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a common factor from a subtraction, pulling it either to the "left" or "right".
        If there are multiple occurrences in any term, the first occurrence is used.
        If groupFactor is True and theFactor is a product, it will be grouped together as a
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.number.multiplication.theorems import distributeThroughSubtractRev
        from proveit.number import Mult
        dummyVar = self.safeDummyVar()
        eq = Equation()
        # commute both terms so that the factor is at the beginning
        factorEqLeft = self.operands[0].factor(theFactor, pull, groupFactor=False, groupRemainder=True,
                                               assumptions=assumptions)
        factorEqRight = self.operands[1].factor(theFactor, pull, groupFactor=False, groupRemainder=True,
                                                assumptions=assumptions)
        # substitute the factored terms
        eq.update(factorEqLeft.substitution(Subtract(dummyVar, self.operands[1]), dummyVar)).checked(assumptions)
        eq.update(factorEqRight.substitution(Subtract(factorEqLeft.rhs, dummyVar), dummyVar)).checked(assumptions)
        # perform distribution in reverse
        num = len(theFactor.operands) if isinstance(theFactor, Mult) else 1
        if pull == 'left':
            wEtcSub = theFactor.operands if isinstance(theFactor, Mult) else [theFactor]
            xSub = factorEqLeft.rhs.operands[num:]
            ySub = factorEqRight.rhs.operands[num:]
            zEtcSub = []
        elif pull == 'right':
            wEtcSub = []
            xSub = factorEqLeft.rhs.operands[:-num]
            ySub = factorEqRight.rhs.operands[:-num]
            zEtcSub = theFactor.operands if isinstance(theFactor, Mult) else [theFactor]
        xSub = xSub[0] if len(xSub) == 1 else Mult(*xSub)
        ySub = ySub[0] if len(ySub) == 1 else Mult(*ySub)
        deduceInComplexes(wEtcSub + [xSub] + [ySub] + zEtcSub, assumptions)
        eq.update(distributeThroughSubtractRev.specialize({wEtc: wEtcSub, x: xSub, y: ySub, zEtc: zEtcSub}))
        if groupFactor and num > 1:
            if pull == 'left':
                eq.update(eq.eqExpr.rhs.group(endIdx=num, assumptions=assumptions))
            elif pull == 'right':
                eq.update(eq.eqExpr.rhs.group(startIdx=-num, assumptions=assumptions))
        return eq.eqExpr.checked(assumptions)

    def convertToAdd(self, assumptions=frozenset()):
        '''
        Given (x - y) deduce and return (x - y) = (x + (-y)).
        Assumptions may be needed to deduce that the operands are in Complexes.
        '''
        from .theorems import subtractAsAddNeg
        deduceInComplexes(self.operands, assumptions)
        return subtractAsAddNeg.specialize({x: self.operands[0], y: self.operands[1]}).checked(assumptions)

    def distribute(self, assumptions=frozenset()):
        '''
        Given something of the form (a + b + ...) - (x + y + ...), deduce and return
        (a + b + ...) - (x + y + ...) = a + b + ... + (-x) + (-y) + ....
        Assumptions may be needed to deduce that the operands are in Complexes.
        '''
        # first deduce: (a + b + ...) - (x + y + ...)  = (a + b + ...) + (-x) + (-y) + ...
        from proveit.number import Add
        eqn = Equation()
        if isinstance(self.operands[1], Add):
            from .theorems import distributeSubtraction
            deduceInComplexes(self.operands[0], assumptions)
            deduceInComplexes(self.operands[1].operands, assumptions)
            eqn.update(distributeSubtraction.specialize({x: self.operands[0], yEtc: self.operands[1].operands}).checked(
                assumptions))
        else:
            eqn.update(self.convertToAdd(assumptions))
        expr = eqn.eqExpr.rhs
        dummyVar = expr.safeDummyVar()
        # next try to simplify any of the negated terms
        negatedTerms = [term for term in expr.operands[1:]]
        for k, negatedTerm in enumerate(negatedTerms):
            try:
                negTermSimplification = negatedTerm.simplification(assumptions)
                eqn.update(
                    negTermSimplification.substitution(Add(*(expr.terms[:k + 1] + [dummyVar] + expr.terms[k + 2:])),
                                                       dummyVar)).checked(assumptions)
                expr = eqn.eqExpr.rhs
            except:
                pass  # skip over
        # ungroup the first part if it is a sum: (a + b + ...) + (-x) + (-y) + ... = a + b + ... + (-x) + (-y) + ...
        if isinstance(self.operands[0], Add):
            eqn.update(expr.applyTransitivity(expr.ungroup(0)).checked(assumptions))
        return eqn.eqExpr

    def cancel(self, assumptions=frozenset()):
        '''
        Attempt to cancel any term of a subtraction and return the resulting equivalence.
        The first term on the left that is the same as on the right will be canceled.
        Assumptions may be needed to deduce that the operands are in Complexes.
        '''
        from .theorems import subtractCancelElimSums, subtractCancelElimLeftSum, subtractCancelElimRightSum
        from .theorems import subtractCancelTwoSums, subtractCancelLeftSum, subtractCancelRightSum
        from .theorems import subtractCancelLeftSumSingleRight, subtractCancelLeftSumSingleLeft, \
            subtractCancelRightSumSingleRight, subtractCancelRightSumSingleLeft
        from .theorems import subtractCancelComplete
        from proveit.number import Add, Neg
        dummy = self.safeDummyVar()
        eq = Equation()
        expr = self
        if self.operands[0] == self.operands[1]:
            # x - x = 0
            deduceInComplexes(self.operands[0], assumptions)
            return subtractCancelComplete.specialize({x: self.operands[0]}).checked(assumptions)
        if isinstance(expr.operands[0], Subtract):
            eq.update(
                expr.operands[0].convertToAdd(assumptions=assumptions).substitution(Subtract(dummy, expr.operands[1]),
                                                                                    dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[1], Subtract):
            eq.update(
                expr.operands[1].convertToAdd(assumptions=assumptions).substitution(Subtract(expr.operands[0], dummy),
                                                                                    dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[0], Add):
            if isinstance(expr.operands[1], Add):
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)
                foundOne = False
                for idx1 in range(len(expr.operands[0].operands)):
                    try:
                        idx2 = expr.operands[1].operands.index(expr.operands[0].operands[idx1])
                        foundOne = True
                        break
                    except:
                        pass
                if not foundOne:
                    raise Exception("No common term found")
                wSub = expr.operands[0].operands[idx1]
                try:
                    idx2 = expr.operands[1].operands.index(wSub)
                except:
                    raise Exception(str(wSub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")
                if len(expr.operands[0].operands) == 2 and len(expr.operands[1].operands) == 2:
                    # special case where Add on both sides is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(
                            Subtract(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(
                            Subtract(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[
                        0]  # the form we were supposed to get to
                    eq.update(subtractCancelElimSums.specialize(
                        {x: expr.operands[0].operands[0], y: expr.operands[0].operands[1],
                         z: expr.operands[1].operands[1]}))
                elif len(expr.operands[0].operands) == 2:
                    # special case where Add on the left is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(
                            Subtract(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[
                        idx2]  # the form we were supposed to get to
                    wSub = expr.operands[0].operands[0]
                    xSub = expr.operands[0].operands[1]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2 + 1:]
                    eq.update(subtractCancelElimLeftSum.specialize({w: wSub, x: xSub, yEtc: ySub, zEtc: zSub}))
                elif len(expr.operands[1].operands) == 2:
                    # special case where Add on the right is eliminated
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(
                            Subtract(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[1].operands[0] == expr.operands[0].operands[
                        idx1]  # the form we were supposed to get to
                    wSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1]
                    ySub = expr.operands[0].operands[idx1 + 1:]
                    zSub = expr.operands[1].operands[1]
                    eq.update(subtractCancelElimRightSum.specialize({wEtc: wSub, x: xSub, yEtc: ySub, z: zSub}))
                else:
                    vSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1 + 1:]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2 + 1:]
                    eq.update(subtractCancelTwoSums.specialize(
                        {vEtc: vSub, w: wSub, xEtc: xSub, yEtc: ySub, zEtc: zSub}).checked(assumptions))
            else:
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1], assumptions=assumptions)
                ySub = expr.operands[1]
                try:
                    idx1 = expr.operands[0].operands.index(ySub)
                except:
                    raise Exception(str(ySub) + " not found in " + str(expr.operands[0]) + " for a subtraction cancel")
                if len(expr.operands[0].operands) == 2:
                    # only one term remains
                    if idx1 == 0:
                        eq.update(subtractCancelLeftSumSingleRight.specialize(
                            {y: ySub, x: expr.operands[0].operands[1]})).checked(assumptions)
                    else:
                        eq.update(subtractCancelLeftSumSingleLeft.specialize(
                            {y: ySub, x: expr.operands[0].operands[0]})).checked(assumptions)
                else:
                    xSub = expr.operands[0].operands[:idx1]
                    zSub = expr.operands[0].operands[idx1 + 1:]
                    eq.update(subtractCancelLeftSum.specialize({xEtc: xSub, y: ySub, zEtc: zSub}).checked(assumptions))
        else:
            deduceInComplexes(expr.operands[0], assumptions=assumptions)
            deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)
            ySub = expr.operands[0]
            try:
                idx2 = expr.operands[1].operands.index(ySub)
            except:
                raise Exception(str(ySub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")
            if len(expr.operands[1].operands) == 2:
                # only one term remains
                if idx2 == 0:
                    eq.update(subtractCancelRightSumSingleRight.specialize(
                        {y: ySub, x: expr.operands[1].operands[1]})).checked(assumptions)
                else:
                    eq.update(subtractCancelRightSumSingleLeft.specialize(
                        {y: ySub, x: expr.operands[1].operands[0]})).checked(assumptions)
            else:
                xSub = expr.operands[1].operands[:idx2]
                zSub = expr.operands[1].operands[idx2 + 1:]
                eq.update(subtractCancelRightSum.specialize({xEtc: xSub, y: ySub, zEtc: zSub}).checked(assumptions))
        if isinstance(eq.eqExpr.rhs, Neg) and (isinstance(eq.eqExpr.rhs.operand, Neg) or eq.eqExpr.rhs.operand == zero):
            eq.update(eq.eqExpr.rhs.simplification(assumptions))  # take care of double negation or zero negation
        return eq.eqExpr
    """

def Subtract(one, two):
    from proveit.number import Neg
    return Add(one, Neg(two)).withStyles(addition='Subtract')

class InnerAddition(DistributiveInnerExprMixin, CommutativeAndAssociativeInnerExprMixin, InnerExprMethodsObject):
    def __init__(self, innerExpr):
        InnerExprMethodsObject.__init__(self, innerExpr)
        if not isinstance(self.expr, Add):
            raise TypeError("InnerAddition is expecting an Add object as the inner expression")
