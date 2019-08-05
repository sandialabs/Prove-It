from proveit import Literal, Operation, USE_DEFAULTS,StyleOptions, maybeFencedLatex, ProofFailure
from proveit._common_ import a, b, c, l, m, n, x, y, AA, BB, CC, A, B, C
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit.number.numeral.deci import DIGITS
import proveit.number.numeral.deci._theorems_

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

    def styleOptions(self):
        # Added by JML on 9/10/19
        options = StyleOptions(self)
        options.add('addition', "'Subtract': uses '-'; 'Add': uses + ")
        return options

    '''
    def string(self, **kwargs):
        from proveit import Iter
        outStr = ''

        if self.getStyle('addition') == 'Subtract':
            # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
            outStr += str(self.operands[0]) + ' - ' + str(self.operands[1].operand)
            return outStr
        else:
            outStr += str(self.operands[0]) + ' + ' + str(self.operands[1])  # normal addition
            return outStr

    def latex(self, **kwargs):
        # Added by JML on 9/10/19
        if self.getStyle('addition') == 'Subtract':
            # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
            kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
            return maybeFencedLatex(self.operands[0].latex() + '-' +self.operands[1].operand.latex(), **kwargs)
        else:
            return Operation.latex(self,**kwargs) # normal addition
    '''
    def remakeConstructor(self):
        # Added by JML on 9/10/19
        if self.getStyle('addition') == 'Subtract':
            return 'Subtract'  # use a different constructor if using the subtraction style
        return Operation.remakeConstructor(self)

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
    def sideEffects(self, knownTruth):
        '''
        side effects for addition
        added by JML on 9/10/19
        '''
        #print("sideEffects")
        from proveit.number import zero
        #print("deriving zero from neg self")
        yield self.deriveZeroFromNegSelf
        if (self.terms[0] == zero or self.terms[1] == zero) and len(self.terms) == 2:
           # print("deducing add zero")
            yield self.deduceAddZero


    def equalitySideEffects(self, knownTruth):
        '''
        Record the knownTruth in Add.knownEqualities, associated for
        each term.
        '''
        #print("equality side Effects on", self)
        from proveit.number import Neg, zero
        if isinstance(self.operands[0], Neg):
            #print("there is a neg:", self)
            return
        if len(self.operands) > 1:
            if isinstance(self.operands[1], Neg):
                # print("there is a neg:", self)
                return
        addition = knownTruth.lhs
        if not isinstance(addition, Add):
            raise ValueError("Expecting lhs of knownTruth to be of an Add expression")
        for term in addition.terms:
            #print("adding known equalities:", term)
            Add.knownEqualities.setdefault(term, set()).add(knownTruth)

        if len(addition.terms)==2:
            # deduce the subtraction form: c-b=a from a+b=c
            #print("deducing subtraction terms:", self)
            yield (lambda assumptions : self.deduceSubtraction(knownTruth.rhs, assumptions))
        

    def concludeStrictIncAdd(self, b, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19

        '''
        from ._theorems_ import strictlyIncreasingAdditions
        from proveit._common_ import m, n, AA, B, CC
        from proveit.number import num
        print(b)
        for i, term in enumerate(self.terms):
            if term == b:
                idx = i
        nVal = len(self.terms) -1 - idx
        print(strictlyIncreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx+1:]}, assumptions=assumptions))
        return strictlyIncreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx +1:]}, assumptions=assumptions)

    def concludeStrictDecAdd(self, b, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19

        '''
        from ._theorems_ import strictlyDecreasingAdditions
        from proveit._common_ import m, n, AA, B, CC
        from proveit.number import num
        print(b)
        print(self.terms)
        for i, term in enumerate(self.terms):
            if term == b:
                idx = i
        nVal = len(self.terms) -1 - idx
        print(nVal)
        return strictlyDecreasingAdditions.specialize({m:num(idx),n:num(nVal),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx +1:]}, assumptions=assumptions)


    def deduceSubtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        #print(self)
        from proveit.number.addition.subtraction._theorems_ import subtractFromAdd
        if len(self.terms) != 2:
            raise Exception("deduceSubtraction implemented only when there are two and only two added terms")
        deduction = subtractFromAdd.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
        #print("deduction", deduction)
        return deduction

    def deriveMultDef(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/25/19
        Given the addition of the same values, derive the multiplication
        a + a + a = 3 * a
        '''
        from proveit.number import num, Mult

        for operand in self.operands:
            if self.operands[0] != operand:
                raise ValueError("Expecting inputs to be equal to each other.")
        return Mult(num(len(self.operands)), self.operands[0]).concludeMultDef(self, assumptions)
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
            print("operand", operand)
            print("expr.operands", expr.operands)

            if i == idx:
                # we have reached the indicated term
                started = True
            if expr.operands[idx] != operand and started:
                # once we reach an operand that is not equal, break
                end = i
                break

        print("end", end)
        print("expr, idx", expr, idx)
        print("l", num(idx))
        print("m", num(len(expr.operands[idx:end])))
        print("n", num(len(expr.operands[end+1:])))
        print("aa", expr.operands[:idx])
        print("bb", expr.operands[idx:end])
        print("cc", expr.operands[end + 1:])
        print("x", expr.operands[idx])
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

    def deriveSwap(self, i, j, assumptions=USE_DEFAULTS):
        '''
        From (A + ... + H + I + J + ... + L + M + N + ... + Q), assuming in Booleans and given
        the beginning and end of the groups to be switched,
        derive and return (A + ... + H + M + J + ... + L + I + N + ... + Q).
        Created by JML on 7/17/19
        '''
        from ._theorems_ import swap
        from proveit.number import num
        from proveit._common_ import l,m,n,AA,B,CC,D,EE
        if 0 < i < j <= len(self.terms) - 1:
            return swap.specialize({l: num(i), m: num(j - i - 1), n: num(len(self.terms) - j - 1), AA: self.terms[:i],B: self.terms[i], CC: self.terms[i + 1:j], D: self.terms[j], EE: self.terms[j + 1:]},assumptions=assumptions)
        else:
            raise IndexError("Beginnings and ends must be of the type: 0<i<j<length.")

    def deriveCommutation(self, idx, dest, assumptions=USE_DEFAULTS):
        '''
        A + ... + B + C + ... + D = A + ... + C + B + ... + d
        Take an operand at index one and insert it at index two
        created by JML on 7/29/19
        '''
        from ._theorems_ import commutation
        from proveit._common_ import l,m,n,AA,BB,C,DD
        from proveit.number import num
        if idx < dest:
            A = idx
            Bone = idx + 1
            Btwo = dest
            D = dest

        elif dest < idx:
            A = dest
            Bone = dest
            Btwo = idx
            D = idx + 1
        else:
            raise ValueError("Expecting the index and destination to be different")
        if 0 < idx < dest < len(self.operands) or 0 < dest < idx < len(self.operands) :
            return commutation.specialize(
                {l: num(A), m: num(len(self.operands[Bone:Btwo])), n: num(len(self.operands[D:])),
                 AA: self.operands[:A], C: self.operands[idx], BB: self.operands[Bone:Btwo], DD: self.operands[D:]},
                assumptions=assumptions)
        else:
            raise ValueError("Expecting index and destination to be of the type 0 < index, destination < length")

    def deriveGroup(self, beg, end, assumptions=USE_DEFAULTS):
        '''
        From (A + B + ... + Y + Z), assuming in Reals and given beginning and end of group, derive and return
        (A + B ... + (l + ... + M) + ... + X + Z).
        Created by JML on 7/17/19
        '''
        print("self, beg, end",self,beg,end)
        from ._theorems_ import group
        from proveit.number import num
        from proveit._common_ import l, m, n, AA, BB, CC, DD, EE
        if end <= beg:
            raise IndexError("Beginning and end value must be of the form beginning < end.")
        if end > len(self.operands) -1:
            raise IndexError("End value must be less than length of expression.")
        return group.specialize({l :num(beg), m:num(end - beg + 1), n: num(len(self.terms) - end - 1), AA:self.terms[:beg], BB:self.terms[beg : end + 1], CC: self.terms[end+1:]}, assumptions=assumptions)

    def deriveUnGroup(self, beg, assumptions=USE_DEFAULTS):
        '''
        From (A + B ... + (l + ... + M) + ... + X + Z), assuming in Reals and given beginning and end of group, derive
        and return (A + B + ... + Y + Z).
        Created by JML on 7/25/19
        '''
        from ._theorems_ import unGroup
        from proveit.number import num
        from proveit._common_ import l, m, n, AA, BB, CC, DD, EE
        if beg > len(self.operands) -1:
            raise IndexError("End value must be less than length of expression.")
        if not isinstance(self.operands[beg], Add):
            raise ValueError("Expecting operand at %s to be an add expression" %str(beg))
        return unGroup.specialize({l :num(beg), m:num(len(self.operands[beg].operands)), n: num(len(self.terms) - beg - 1), AA:self.terms[:beg], BB:self.operands[beg].terms[0:], CC: self.terms[beg+1:]}, assumptions=assumptions)

    def deriveZeroFromNegSelf(self, assumptions=USE_DEFAULTS):
        '''
        added by JML on 9/10/19
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
        print("self, idx in addNegSelf", expr, idx)
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
    def createDict(self, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/24/19
        creates a dictionary from an addition expression where the keys are either a literal, or the variables themselves
        '''
        from proveit import Variable
        from proveit.number import one, two, num, Neg, Mult
        from proveit import ExprList
        hold = {}

        other = []
        order = []
        for i, val in enumerate(self.operands):
            # loop through each operand
            neg = False
            # used to differentiate positive and negative for ordering
            if isinstance(val, Mult):
                # place it in the correct place regardless of multiplication
                val = val.operands[1]
            if isinstance(val, Neg):
                # place it in the correct place regardless of negation
                neg = True
                val = val.operands[0]
            if isinstance(val, Add):
                # must be grouped, set other = to the operands
                other = [val.operands]
            elif isinstance(val, Literal):
                # must be a number, put it in key: Lit
                if neg:
                    if "LitNeg" in hold:
                        # if the key is already there, add it to the list of values
                        hold["LitNeg"].append([i,val])
                    else:
                        # if not create the key and add the value
                        hold["LitNeg"] = [[i, val]]
                        if "Lit" in order:
                            # if there is a positive value already, add the negative value after it.
                            order.insert(order.index("Lit") + 1,"LitNeg")
                        else:
                            # if not, just add the negative value
                            order.append("LitNeg")
                else:
                    if "Lit" in hold:
                        # if the key is already there, add it to the list of values
                        hold["Lit"].append([i,val])
                    else:
                        # if not, create the key and add the value
                        hold["Lit"] = [[i, val]]
                        if "LitNeg" in order:
                            # if there is already a negative value, add the positive value before it.
                            order.insert(order.index("LitNeg"),"Lit")
                        else:
                            # if not, just add the value to the end.
                            order.append("Lit")
            elif isinstance(val, Variable):
                # is a variable, either create a new key  or put in existing key
                if neg:
                    key = Neg(val)
                    if key in hold:
                        # if the key is already there, add it to the list of values
                        hold[Neg(val)].append([i,one])
                    else:
                        # if not, create the key and add the value
                        hold[Neg(val)] = [[i, one]]
                        if val in order:
                            # if there is already a positive value, add the negative value after it.
                            order.insert(order.index(val) + 1, Neg(val))
                        else:
                            # if not, just add the negative value
                            order.append(Neg(val))
                else:
                    if val in hold:
                        # if the key exists, just add the value to the list
                        hold[val].append([i,one])
                    else:
                        # if not, create the key and add the value
                        hold[val] = [[i, one]]
                        key = Neg(val)
                        if key in order:
                            # if the negative value is already there, add the positive value before it.
                            order.insert(order.index(key),val)
                        else:
                            # if not, just add the positive value key
                            order.append(val)
            else:
                raise ValueError("simplification not implemented for %s in Add" %str(val))
            if len(other) != 0:
                # there is a group of values
                val = other[0][0]
                if isinstance(val, Mult):
                    # place it in the correct place regardless of multiplication
                    val = val.operands[1]
                if isinstance(val, Neg):
                    val = other[0][0].operand
                    neg = True
                if isinstance(val, Literal):
                    # if the group is a literal, put it in Lit
                    if neg:
                        if "LitNeg" in hold:
                            # if the key is already there, add it to the list of values
                            hold["LitNeg"].append([i, other])
                        else:
                            # if not create the key and add the value
                            hold["LitNeg"] = [[i, other]]
                            if "Lit" in order:
                                # if there is a positive value already, add the negative value after it.
                                order.insert(order.index("Lit") + 1, "LitNeg")
                            else:
                                # if not, just add the negative value
                                order.append("LitNeg")
                    else:
                        if "Lit" in hold:
                            # if the key is already there, add it to the list of values
                            hold["Lit"].append([i, other])
                        else:
                            # if not, create the key and add the value
                            hold["Lit"] = [[i, other]]
                            if "LitNeg" in order:
                                # if there is already a negative value, add the positive value before it.
                                order.insert(order.index("LitNeg"), "Lit")
                            else:
                                # if not, just add the value to the end.
                                order.append("Lit")
                elif isinstance(val, Variable):
                    # if its a variable, check to see if a key already exists
                    if neg:
                        if val in hold:
                            # if the key is already there, add it to the list of values
                            hold[Neg(val)].append([i, num(len(other[0]))])
                        else:
                            # if not, create the key and add the value
                            hold[Neg(val)] = [[i, num(len(other[0]))]]
                            if val in order:
                                # if there is already a positive value, add the negative value after it.
                                order.insert(order.index(val) + 1, Neg(val))
                            else:
                                # if not, just add the negative value
                                order.append(Neg(val))
                    else:
                        if val in hold:
                            # if the key exists, just add the value to the list
                            hold[val].append([i, num(len(other[0]))])
                        else:
                            # if not, create the key and add the value
                            hold[val] = [[i, num(len(other[0]))]]
                            key = Neg(val)
                            if key in order:
                                # if the negative value is already there, add the positive value before it.
                                order.insert(order.index(key), val)
                            else:
                                # if not, just add the positive value key
                                order.append(val)
            other = []
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
                    print(One, Two)

                    idx += 1
                    print("in loop idx, m, length", idx, m, length)
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
                print("one, two, idx", One,Two,idx)
                # if we incremented at least once, we need to subtract 1 because the last value was not equal
                Two = expr.operands[m + idx]
                if isinstance(Two, Mult):
                    Two = Two.operands[1]
                # redefine two to reflect the end of the group

                if One == Two or (isinstance(One, Literal) and isinstance(Two, Literal)):
                    # as long as the first and last are equal, we assume anything in between is as well because
                    # we checked above. Derive the group from one to two
                    print("deriving group, expr, m , m+idx", expr, m, m+idx)
                    expr = expr.deriveGroup(m, m + idx, assumptions).rhs
                    length -= idx
                    # we account for the change in length because of the grouping
            m += 1
            # move on to the next value after the group
        return expr

    def simplifications(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/24/19
        combine like terms
        '''
        from proveit import Variable
        from proveit.number import zero, one, Neg, Mult
        from proveit.logic import Equals

        expr = self
        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                print("to ungroup")
                expr = expr.deriveUnGroup(n, assumptions).rhs
                print(550)
                print(Equals(self, expr).prove(assumptions))
                print("new expr", expr)
            length = len(expr.operands)
            n += 1
        print("expr after initial ungroup",expr)
        # separate the types of operands in a dictionary
        hold, firstOrder = expr.createDict(assumptions)
        order = firstOrder
        print("order", order)
        # Group like terms
        for j, key in enumerate(order):
            # loop through all the keys (literals, and any variable keys)
            print("before loop",hold[key], key)
            size = len(hold[key])
            for l, item in enumerate(hold[key]):
                place = l
                # loop through all the values in each key
                print("in loop, place, item, size (place < size)", place, item, size-1)
                if place < size:
                    # ensures that we cycle through all of the values for each key despite the changing length of
                    # each key because of grouping.
                    if place != len(hold[key]) - 1:
                        # this if statement ensures that we don't go out of the range of values for each key
                        print("before if", hold[key][place][0], hold[key][place+1][0] - 1)
                        if hold[key][place][0] != hold[key][place+1][0] - 1:
                            # if the index of the first item in the values is not one less than the index of the second value,
                            # then they are not next to each other in the expression.

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

                            # Swap the second value with whatever is next to the first item.
                            print("place", place)
                            print("in if", hold[key][place][0], hold[key][place+1][0])
                            print("swap values",hold[key][place+1][0],hold[key][place][0]+1)
                            print(expr.deriveCommutation(hold[key][place + 1][0], hold[key][place][0] + 1,
                                                         assumptions=assumptions))
                            if hold[key][place + 1][0] < hold[key][place][0] + 1:
                                expr = expr.deriveCommutation(hold[key][place + 1][0], hold[key][place][0] + 1,assumptions=assumptions).rhs
                            if hold[key][place + 1][0] > hold[key][place][0] + 1:
                                expr = expr.deriveCommutation(hold[key][place + 1][0], hold[key][place][0] + 1,
                                                              assumptions=assumptions).lhs
                            print(603, expr)
                            print(Equals(self, expr).prove(assumptions))
                            # rewrite the dictionary to reflect this change
                            hold, no = expr.createDict(assumptions)
                            print("new dict after swap", hold)
                    elif j + 1 < len(order) and hold[order[j]][len(hold[order[j]])-1][0] + 1 != hold[order[j + 1]][0][0]:
                        # make sure that the next variable is right next to the previous one.
                        print("j", j)
                        print("order[j]", order[j])
                        print("hold", hold)
                        print("in else", hold[order[j]][len(hold[order[j]])-1][0], hold[order[j + 1]][0][0])
                        print("swap values", hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1)
                        print(expr.deriveCommutation(hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1,
                                                     assumptions=assumptions))
                        if hold[order[j + 1]][0][0] < hold[order[j]][len(hold[order[j]])-1][0] + 1:
                            expr = expr.deriveCommutation(hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1,
                                                          assumptions=assumptions).rhs
                            print("rhs")
                        if hold[order[j + 1]][0][0] > hold[order[j]][len(hold[order[j]])-1][0] + 1:
                            expr = expr.deriveCommutation(hold[order[j + 1]][0][0] , hold[order[j]][len(hold[order[j]])-1][0] + 1,
                                                          assumptions=assumptions).lhs
                            print("lhs")
                        print(603, expr)
                        print(Equals(self, expr).prove(assumptions))
                        # rewrite the dictionary to reflect this change
                        hold, no = expr.createDict(assumptions)
                        print("new dict after swap", hold)
                        break
                print("looping again", l, hold[key])

        # combine like terms
        # cancel negated terms if it can be done
        # j acts as a more accurate count of i
        j = 0
        for i, operand in enumerate(expr.operands):
            # loop through all the operands
            if isinstance(operand, Neg):
                # the operand is negated
                print("expr, operand, j", expr, operand, j)
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
                    print("j", j)
                    expr = expr.deriveGroup(j,j+1, assumptions).rhs
                    print(702)
                    print(Equals(self, expr).prove(assumptions))
                    print(expr)
                    sub = expr.operands[j].deriveZeroFromNegSelf(assumptions)
                    expr = sub.substitution(expr.innerExpr().operands[j], assumptions=assumptions).rhs
                    print(707)
                    print(Equals(self, expr).prove(assumptions))
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
                    print("j",j)
                    expr = expr.deriveGroup(j-1, j, assumptions).rhs
                    print(725)
                    print(Equals(self, expr).prove(assumptions))
                    print(expr)
                    sub = expr.operands[j-1].deriveZeroFromNegSelf(assumptions)
                    expr = sub.substitution(expr.innerExpr().operands[j-1], assumptions=assumptions).rhs
                    print(730)
                    print(Equals(self, expr).prove(assumptions))
                    # accounts for the change of the length of the expression after the cancellation
                    j-=1
            # moving on to the next term
            j += 1

        # group the terms so we can easily combine them
        expr = expr.groupLikeTerms(assumptions)
        print(739)
        print(Equals(self, expr).prove(assumptions))
        print("expr after group like terms", expr)
        # rewrite the dictionary to reflect this change
        hold,no = expr.createDict(assumptions)
        print("new dict after group", hold)
        print("order", order)

        # combine like terms by multiplying
        for key in order:
            # loop through all the different types of terms
            print("key",key)
            if key != "Lit" and key != "LitNeg" :
                # for all the keys that are not literals, derive the multiplication from the addition
                print("hold[key][0][0]", hold[key][0][0])
                if isinstance(expr.operands[hold[key][0][0]], Add):
                    '''
                    idx = hold[key][0][0]
                    print(idx)
                    print(expr.operands[idx].deriveMultDef(assumptions))
                    sub = expr.operands[idx].deriveMultDef(assumptions)
                    print(expr)
                    print(expr.innerExpr())
                    print(expr.innerExpr().operands[idx])
                    print(sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions))
                    expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).rhs
                    print("expr before equals",expr)
                    print(689)
                    Equals(self, expr).prove(assumptions)
                    # rewrite the dictionary to reflect this change
                    hold,no = expr.createDict(assumptions)
                    print("new dict after mult", hold)
                    print("order", order)
                    '''
                    idx = hold[key][0][0]
                    print("idx",idx)
                    print("operand at idx", expr.operands[idx])
                    # make sure all the operands in the key are products (multiplication)
                    if isinstance(expr.operands[idx], Add):
                        # if it's grouped, send it to become a multiplication
                        sub = expr.operands[idx].createMult(assumptions)
                        print("sub for mult", sub)
                        expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).lhs
                        print("new expr after mult", expr)
                        print(780)
                        print(Equals(self, expr).prove(assumptions))
                    print("factor operand at idx", expr.operands[idx].factor(key, assumptions=assumptions))
                    sub = expr.operands[idx].factor(key, assumptions=assumptions)
                    print("sub", sub)
                    print("expr", expr)
                    print("expr.innerExpr()", expr.innerExpr())
                    print("expr.innerExpr().operands[idx]", expr.innerExpr().operands[idx])
                    print("the substitution", sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions))
                    expr = sub.substitution(expr.innerExpr().operands[idx], assumptions=assumptions).lhs
                    print("expr before equals", expr)
                    print(785)
                    print(Equals(self, expr).prove(assumptions))
                    # rewrite the dictionary to reflect this change
                    print("expr.operands[hold[key][0][0]].operands",expr.operands[hold[key][0][0]].operands)
                    hold, no = expr.createDict(assumptions)
                    print("new dict after mult", hold)
                    print("order", order)
            else:
                pass
        print("expr after mult", expr)
        '''
        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                print("to ungroup")
                expr = expr.deriveUnGroup(n, assumptions).rhs
                print(804)
                print(Equals(self, expr).prove(assumptions))
                print("new expr", expr)
            length = len(expr.operands)
            n += 1
        '''
        for i, operand in enumerate(expr.operands):
            print("expr, i, length", expr, i, length)
            if isinstance(operand, Add):
                sub = expr.operands[i].evaluations(assumptions)
                expr = sub.substitution(expr.innerExpr().operands[i], assumptions).rhs
                print(Equals(self, expr).prove(assumptions))

            elif isinstance(operand, Mult):
                if isinstance(operand.operands[0], Add):
                    sub = expr.operands[i].operands[0].evaluations(assumptions)
                    expr = sub.substitution(expr.innerExpr().operands[i].operands[0], assumptions).rhs
                    print(Equals(self, expr).prove(assumptions))
                if isinstance(expr.operands[i].operands[0], Add) and len(expr.operands[i].operands[0].operands) == 1:
                    from proveit.number.addition._axioms_ import singleAdd
                    sub = singleAdd.specialize({x:expr.operands[i].operands[0].operands[0]})
                    print("single Add", sub)
                    expr = sub.substitution(expr.innerExpr().operands[i].operands[0], assumptions).rhs
                    print("after single Add", expr)
                    print(Equals(self,expr).prove(assumptions))

        # ungroup the expression
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            print("n, length", n, length)
            if isinstance(expr.operands[n], Add):
                # if it is grouped, ungroup it
                print("to ungroup")
                expr = expr.deriveUnGroup(n, assumptions).rhs
                print(844)
                print(Equals(self, expr).prove(assumptions))
                print("new expr", expr)
            length = len(expr.operands)
            n += 1
        print("expr after initial ungroup", expr)
        print("expr after evaluation", expr)
        print("last equals!")
        return Equals(self,expr).prove(assumptions)

    def evaluations(self, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/31/19
        evaluate literals in a given expression (used for simplification)
        '''
        from proveit.logic import Equals, EvaluationError
        from proveit.number import Numeral
        expr = self
        length = len(expr.operands)
        i = 0
        import pdb # for tracing
        #pdb.set_trace()  # BREAKPOINT
        if length == 2:

            try:
                expr = expr.evaluation(assumptions).rhs
                print(Equals(self, expr).prove(assumptions))
                return Equals(self, expr).prove(assumptions)
            except EvaluationError:
                print("return 883")
                if isinstance(expr.operands[0], Literal) and isinstance(expr.operands[1], Literal):
                    raise EvaluationError("Unable to evaluate %s, evaluation is not implemented for a sum greater than 9" % str(expr))
                else:
                    raise EvaluationError(
                        "Unable to evaluate %s, simplification not implemented for variable coefficients." % str(
                            expr))
        while i < length:
           # if not isinstance(expr.operands[i], Literal):
               # raise ValueError("expecting addition of literals")
            if i + 1 < length:
               # if not isinstance(expr.operands[i + 1], Literal):
                  #  raise ValueError("expecting addition of literals")
                expr = expr.deriveGroup(i, i + 1, assumptions).rhs
                print("after group in evaluations", Equals(self, expr).prove(assumptions))
                #pdb.set_trace()  # BREAKPOINT
                try:
                    sub = expr.operands[i].evaluation(assumptions)
                    print(sub)
                    expr = sub.substitution(expr.innerExpr().operands[i], assumptions).rhs
                    print(Equals(self, expr).prove(assumptions))

                except EvaluationError:
                    literal = True
                    for operand in expr.operands[i].operands:
                        if not isinstance(operand, Literal):
                            literal = False
                    if not literal:
                        raise EvaluationError("Unable to evaluate %s, simplification not implemented for variable coefficients"%str(expr.operands[i]))
                    else:
                        raise EvaluationError("Unable to evaluate %s, evaluation not implemented for a sum greater than 9"%str(expr.operands[i]))

                    pass
                length -=1
            else:
                break
        print(expr)

        print("return 894")
        return Equals(self, expr).prove(assumptions)
    """
    def simplification(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive and return this Add expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from ._theorems_ import addZero
        eq = Equation()
        expr = self
        try:
            zeroIdx = expr.operands.index(zero)
            # there is a zero in the sum.  We can simplify that.
            if zeroIdx > 0:
                # commute it so that the zero comes first
                expr = eq.update(expr.commute(0, zeroIdx, zeroIdx, zeroIdx+1, assumptions)).rhs
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(addZero.specialize({x:expr.operands[1]}))
        except ValueError:
            raise ValueError('Only trivial simplification is implemented (zero term)')


    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive this Add expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    """
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
                    print(b)
                    break
                except ProofFailure:
                    pass
            if val == -1:
                raise ValueError("Expecting at least one value to be greater than zero")
            print(len(self.operands))
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
        
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from ._theorems_ import addComm
        if startIdx1 is None and endIdx1 is None and startIdx2 is None and endIdx2 is None:
            stattIdx1, endIdx1, startIdx2, endIdx2 = 0, 1, 1, None
        nOperands = len(self.operands)
        start1, stop1, _ = slice(startIdx1, endIdx1).indices(nOperands)
        start2, stop2, _ = slice(startIdx2, endIdx2).indices(nOperands)
        if start1  > start2:
            # swap 1 and 2 so that 1 comes first
            startIdx1, endIdx1, startIdx2, endIdx2 = startIdx2, endIdx2, startIdx1, endIdx2
            start1, stop1, start2, stop2 = start2, stop2, start1, stop1
        if stop1 > start2:
            raise ValueError("Cannot commute verlapping sets of operands")
        vSub = self.operands[:startIdx1] if startIdx1 is not None else []
        wSub = self.operands[startIdx1:endIdx1]
        xSub = self.operands[endIdx1:startIdx2]
        ySub = self.operands[startIdx2:endIdx2]
        zSub = self.operands[endIdx2:] if endIdx2 is not None else []
        deduceInComplexes(self.operands, assumptions)
        return addComm.specialize({vEtc:vSub, wEtc:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}, assumptions=assumptions)
    """
    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-sum wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from axioms import addAssoc
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:startIdx] if startIdx is not None else []
        ySub = self.operands[startIdx:endIdx]
        zSub = self.operands[endIdx:] if endIdx is not None else []
        return addAssoc.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def ungroup(self, idx, assumptions=frozenset()):
        '''
        Ungroup (un-associate a sub-sum wrapped in parenthesis)
        an operand, self.operands[idx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        if not isinstance(self.operands[idx], Add):  
            raise ValueError("Selected term is not an Add expression")

        from theorems import addAssocRev
        deduceInComplexes(self.operands, assumptions)
        deduceInComplexes(self.operands[idx].operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return addAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)
    """

    def createMult(self, assumptions=USE_DEFAULTS):
        '''
        given an expression, turn all the operands into multiplication
        created by JML on 7/31/19
        '''
        from proveit.number.multiplication._theorems_ import distributeThroughSum, multOne
        from proveit.number import num, Mult, one, Neg
        from proveit.logic import Equals
        from proveit import Variable
        expr = self
        for k, operand in enumerate(expr.operands):
            # loop through all the operands
            print("expr", expr)
            print(operand)
            if isinstance(operand, Neg):
                # turn it into 1 * the factor
                from proveit.number.negation._axioms_ import negMultOneDef
                print(negMultOneDef.specialize({x:operand.operand}, assumptions=assumptions))
                sub = negMultOneDef.specialize({x:operand.operand}, assumptions=assumptions)
                print("done with sub", sub)
                expr = sub.substitution(expr.innerExpr().operands[k], assumptions).rhs
                print("did expr", expr)
                print(1045)
                Equals(self, expr).prove(assumptions)
                print(Equals(self, expr).prove(assumptions))
                operand = expr.operands[k]
            elif isinstance(operand, Variable):
                # turn it into 1 * the factor
                sub = multOne.specialize({x: expr.operands[k]}, assumptions=assumptions)
                print("sub", sub)
                # sub = Add(expr.operands[k]).deriveMultDef(assumptions)
                # print(sub)
                print("substitution", sub.substitution(expr.innerExpr().operands[k], assumptions))
                expr = sub.substitution(expr.innerExpr().operands[k], assumptions).lhs
                print(1058)
                Equals(self, expr).prove(assumptions)
                print(Equals(self, expr).prove(assumptions))
                operand = expr.operands[k]
            print("operand after mult change",operand)
            print("new expr", expr)
        return Equals(self, expr).prove(assumptions)

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
            print("expr", expr)
            print(operand)
            if isinstance(operand, Mult):
                print("operand is mult")
                for i, term in enumerate(operand.operands):
                    print(i, term)
                    # loop through the operands of mult
                    print("operand.operands[:i}", operand.operands[:i])
                    if term == theFactor:
                        numberOfFactors +=1
                        coefficient.extend(operand.operands[:i])
                        if i + 1 < len(operand.operands):
                            after.extend(operand.operands[i+1:])

        if pull == "left":
            b = coefficient
            a = after
        else:
            b = after
            a = coefficient

        print("l", num(len(a)))
        print("m", num(len(b)))
        print("n", one)
        print("aa", a)
        print("bb", b)
        print("cc",theFactor)
        print(1045)
        Equals(self, expr).prove(assumptions)
        print(Equals(self, expr).prove(assumptions))
        return distributeThroughSum.specialize({l:num(len(a)),m:num(len(b)),n:one,AA:a,BB:b,CC:[theFactor]}, assumptions=assumptions)
    """
    def factor(self, theFactor, pull="left", groupFactor=True, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this sum, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, these operands are grouped 
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.number.multiplication._theorems_ import distributeThroughSum
        from proveit.number import num
        expr = self
        eq = Equation()
        dummyVar = self.safeDummyVar()
        yEtcSub = []
        for i, term in enumerate(self.terms):
            sumWithDummy = Add(*[jterm if j != i else dummyVar for j, jterm in enumerate(expr.terms)])
            termFactorization = term.factor(theFactor, pull, groupFactor=groupFactor, groupRemainder=True, assumptions=assumptions)
            if not isinstance(termFactorization.rhs, Multiply):
                raise Exception('Expecting right hand size of factorization to be a product')
            if pull == 'left':
                # the grouped remainder on the right
                yEtcSub.append(termFactorization.rhs.operands[-1]) 
            else:
                # the grouped remainder on the left
                yEtcSub.append(termFactorization.rhs.operands[0])
            eq.update(termFactorization.substitution(sumWithDummy, dummyVar))
            expr = eq.eqExpr.rhs
        if not groupFactor and isinstance(theFactor, Multiply):
            factorSub = theFactor.operands
        else:
            factorSub = [theFactor]
        deduceInComplexes(factorSub, assumptions=assumptions)
        deduceInComplexes(yEtcSub, assumptions=assumptions)
        if pull == 'left':
            xEtcSub = factorSub
            zEtcSub = []
        else:
            xEtcSub = []
            zEtcSub = factorSub
        eq.update(distributeThroughSumRev.specialize({l:num(len(xEtcSub)),m:num(len(yEtcSub)),n:num(len(zEtcSub)),AA:xEtcSub, BB:yEtcSub, CC:zEtcSub}, assumptions=assumptions))
        return eq.eqExpr.checked(assumptions)
    """
    def join(self, assumptions=frozenset()):
        '''
        For joining two summations (could be more sophisticated later).
        '''
        from proveit.number import Sum
        if len(self.terms) != 2 or not all(isinstance(term, Sum) for term in self.terms):
            raise Exception("Sum joining currently only implemented for two summation terms.")
        return self.terms[0].join(self.terms[1], assumptions)

    
    """
    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to numbers, derive and
        return the equality of this expression with the sum of these numbers. 
        '''
        from proveit.number.sets.integer._axioms_ import twoDef, threeDef, fourDef, fiveDef, sixDef, sevenDef, eightDef, nineDef # load in integer successor evaluations  
        for i, operand in enumerate(self.operands):
            if not isIrreducibleValue(operand):
                # The operands are not always true/false, so try the default evaluation method
                # which will attempt to evaluate each of the operands.
                return Operation.evaluation(self, assumptions)
        # TODO
        
        '''
        From disjunction, just brought in as an example
        if len(self.operands) == 2:
            # This will automatically return orTT, orTF, orFT, or orFF
            return Operation.evaluation(self, assumptions)
        if trueIndex >= 0:
            # one operand is TRUE so the whole disjunction evaluate to TRUE.
            return disjunctionTrueEval.specialize({Amulti:self.operands[:trueIndex], Cmulti:self.operands[trueIndex+1:]}, assumptions=assumptions)
        else:
            # no operand is TRUE so the whole disjunction evaluate to FALSE.
            return disjunctionFalseEval.specialize({Amulti:self.operands}, assumptions=assumptions)
        '''
    """


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