from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals
from proveit._common_ import a, b

class Numeral(Literal, IrreducibleValue):
    _inNaturalStmts = None # initializes when needed
    _inNaturalPosStmts = None # initializes when needed
    _inDigitsStmts = None  # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, n, stringFormat=None, latexFormat=None):
        if stringFormat is None: stringFormat=str(n)
        Literal.__init__(self, stringFormat, extraCoreInfo=[str(n)], theory=__file__)
        if not isinstance(n, int):
            raise ValueError("'n' of a Numeral must be an integer")
        self.n = n
    
    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
    
    def notEqual(self, other, assumptions=USE_DEFAULTS):
        from proveit.numbers import Less
        from proveit.numbers.ordering._theorems_ import lessIsNotEq, gtrIsNotEq
        _a, _b = Less.sorted_items([self, other], assumptions=assumptions)
        if self==_a:
            return lessIsNotEq.instantiate({a:_a, b:_b}, assumptions=assumptions)
        else:
            return gtrIsNotEq.instantiate({a:_b, b:_a}, assumptions=assumptions)

    def remakeArguments(self):
        '''
        Yield the argument values that could be used to recreate this DigitLiteral.
        '''
        yield self.n
        if self.stringFormat != str(self.n):
            yield '"' + self.stringFormat + '"'
        if self.latexFormat != self.stringFormat:
            yield ('latexFormat', 'r"' + self.latexFormat + '"')
    
    def asInt(self):
        return self.n
            
    @staticmethod
    def makeLiteral(string_format, latex_format, extra_core_info, theory):
        '''
        Make the DigitLiteral that matches the core information.
        '''
        from proveit import Theory
        assert theory==Theory(__file__), (
                "Expecting a different Theory for a DigitLiteral: "
                "%s vs %s"%(theory.name, Theory(__file__).name))
        n = int(extra_core_info[0])
        return Numeral(n, string_format, latex_format)
     
    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        from proveit.numbers import Natural, NaturalPos, Digits
        from proveit.logic import InSet
        if number_set==Natural:
            return self.deduceInNatural(assumptions)
        elif number_set==NaturalPos:
            return self.deduceInNaturalPos(assumptions)
        elif number_set==Digits:
            return self.deduceInDigits(assumptions)
        else:
            try:
                # Do this to avoid infinite recursion -- if
                # we already know this numeral is in the NaturalPos set
                # we should know how to prove that it is in any
                # number set that contains the natural numbers.
                if self.n > 0:
                    InSet(self, NaturalPos).prove(automation=False)
                else:
                    InSet(self, Natural).prove(automation=False)
            except:
                # Try to prove that it is in the given number
                # set after proving that the numeral is in the
                # Natural set and the NaturalPos set.
                self.deduceInNatural()
                if self.n > 0:
                    self.deduceInNaturalPos()
            return InSet(self, number_set).conclude(assumptions)
        
    def deduceInNatural(self, assumptions=USE_DEFAULTS):
        if Numeral._inNaturalStmts is None:
            from proveit.numbers.number_sets.natural_numbers._axioms_ import zero_in_nats
            from .decimals._theorems_ import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
            Numeral._inNaturalStmts = {0:zero_in_nats, 1:nat1, 2:nat2, 
                                        3:nat3, 4:nat4, 5:nat5, 6:nat6, 
                                        7:nat7, 8:nat8, 9:nat9}
        return Numeral._inNaturalStmts[self.n]
    
    '''
    def deduceNotZero(self):
        if Numeral._notZeroStmts is None:
            from .decimals._theorems_ import oneNotZero, twoNotZero, threeNotZero, fourNotZero, fiveNotZero
            from .decimals._theorems_ import sixNotZero, sevenNotZero, eightNotZero, nineNotZero
            Numeral._notZeroStmts = {1:oneNotZero, 2:twoNotZero, 3:threeNotZero, 4:fourNotZero, 5:fiveNotZero, 6:sixNotZero, 7:sevenNotZero, 8:eightNotZero, 9:nineNotZero}
        return Numeral._notZeroStmts[self.n]
    '''

    def deduceInNaturalPos(self, assumptions=USE_DEFAULTS):
        if Numeral._inNaturalPosStmts is None:
            from .decimals._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5
            from .decimals._theorems_ import posnat6, posnat7, posnat8, posnat9
            Numeral._inNaturalPosStmts = {1:posnat1, 2:posnat2, 3:posnat3, 4:posnat4, 5:posnat5, 6:posnat6, 7:posnat7, 8:posnat8, 9:posnat9}
        if self.n <= 0:
            raise ProofFailure(self, [], 
                               "Cannot prove %d in NaturalPos"%self.n)
        return Numeral._inNaturalPosStmts[self.n]

    def deduceInDigits(self, assumptions=USE_DEFAULTS):
        if Numeral._inDigitsStmts is None:
            from .decimals._theorems_ import digit0, digit1, digit2, digit3, digit4, digit5
            from .decimals._theorems_ import digit6, digit7, digit8, digit9
            Numeral._inDigitsStmts = {0:digit0, 1:digit1, 2:digit2, 3:digit3, 4:digit4, 5:digit5, 6:digit6, 7:digit7, 8:digit8, 9:digit9}
        if self.n < 0 or self.n > 9:
            raise ProofFailure(self, [],
                               "Cannot prove %d in Digits"%self.n)
        return Numeral._inDigitsStmts[self.n]

    def deducePositive(self, assumptions=USE_DEFAULTS):
        if Numeral._positiveStmts is None:
            from .decimals._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5
            from .decimals._theorems_ import posnat6, posnat7, posnat8, posnat9
            Numeral._positiveStmts = {1:posnat1, 2:posnat2, 3:posnat3, 4:posnat4, 5:posnat5, 6:posnat6, 7:posnat7, 8:posnat8, 9:posnat9}
        return Numeral._positiveStmts[self.n]

class NumeralSequence(Operation, IrreducibleValue):
    """
    Base class of BinarySequence, DecimalSequence, and HexSequence.
    """
    def __init__(self, operator, *digits):
        from proveit import ExprRange
        Operation.__init__(self, operator, digits)
        # if len(digits) <= 1 and not isinstance(digits[0], ExprRange):
        #     raise Exception('A NumeralSequence should have two or more digits.  Single digit number should be represented as the corresponding Literal.')
        self.digits = self.operands

    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
    
    def notEqual(self, other, assumptions=USE_DEFAULTS):
        # same method works for Numeral and NumeralSequence.
        return Numeral.notEquals(self, other, assumptions=assumptions)
    
    def _formatted(self, formatType, **kwargs):
        from proveit import ExprRange, varRange
        outstr = ''

        for digit in self.digits:
            if isinstance(digit, Operation):
                outstr += digit.formatted(formatType, fence=True)
            elif isinstance(digit, ExprRange):
                outstr += digit.formatted(formatType, operator=' ')
            else:
                outstr += digit.formatted(formatType)
        return outstr
        #return ''.join(digit.formatted(formatType) for digit in self.digits)

def isLiteralInt(expr):
    from proveit.numbers import Neg
    if isinstance(expr, Numeral):
        return True
    elif isinstance(expr, NumeralSequence):
        return True
    elif isinstance(expr, Neg) and isLiteralInt(expr.operand):
        return True
    return False        