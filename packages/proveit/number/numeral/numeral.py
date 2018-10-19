from proveit import Literal, Operation, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals

class Numeral(Literal, IrreducibleValue):
    _inNaturalsStmts = None # initializes when needed
    _inNaturalsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, n, stringFormat=None, latexFormat=None):
        if stringFormat is None: stringFormat=str(n)
        Literal.__init__(self, stringFormat, extraCoreInfo=[str(n)], context=__file__)
        if not isinstance(n, int):
            raise ValueError("'n' of a Numeral must be an integer")
        self.n = n
    
    def evalEquality(self, other):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals

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
    def makeLiteral(string_format, latex_format, extra_core_info, context):
        '''
        Make the DigitLiteral that matches the core information.
        '''
        from proveit import Context
        assert context==Context(__file__), 'Expecting a different Context for a DigitLiteral'
        n = int(extra_core_info[0])
        return Numeral(n, string_format, latex_format)
     
    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        from proveit.number import Naturals, NaturalsPos
        if number_set==Naturals:
            return self.deduceInNaturals()
        elif number_set==NaturalsPos:
            return self.deduceInNaturalsPos()
        
    def deduceInNaturals(self):
        if Numeral._inNaturalsStmts is None:
            from proveit.number.sets.integer._theorems_ import zeroInNats
            from .decimal._theorems_ import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
            Numeral._inNaturalsStmts = {0:zeroInNats, 1:nat1, 2:nat2, 3:nat3, 4:nat4, 5:nat5, 6:nat6, 7:nat7, 8:nat8, 9:nat9}
        return Numeral._inNaturalsStmts[self.n]
    
    def deduceNotZero(self):
        if Numeral._notZeroStmts is None:
            from .decimal._theorems_ import oneNotZero, twoNotZero, threeNotZero, fourNotZero, fiveNotZero
            from .decimal._theorems_ import sixNotZero, sevenNotZero, eightNotZero, nineNotZero
            Numeral._notZeroStmts = {1:oneNotZero, 2:twoNotZero, 3:threeNotZero, 4:fourNotZero, 5:fiveNotZero, 6:sixNotZero, 7:sevenNotZero, 8:eightNotZero, 9:nineNotZero}
        return Numeral._notZeroStmts[self.n]

    def deduceInNaturalsPos(self):
        if Numeral._inNaturalsPosStmts is None:
            from .decimal._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5
            from .decimal._theorems_ import posnat6, posnat7, posnat8, posnat9
            Numeral._inNaturalsPosStmts = {1:posnat1, 2:posnat2, 3:posnat3, 4:posnat4, 5:posnat5, 6:posnat6, 7:posnat7, 8:posnat8, 9:posnat9}
        return Numeral._inNaturalsPosStmts[self.n]    

    def deducePositive(self):
        if Numeral._positiveStmts is None:
            from .decimal._theorems_ import oneIsPositive, twoIsPositive, threeIsPositive, fourIsPositive, fiveIsPositive
            from .decimal._theorems_ import sixIsPositive, sevenIsPositive, eightIsPositive, nineIsPositive
            Numeral._positiveStmts = {1:oneIsPositive, 2:twoIsPositive, 3:threeIsPositive, 4:fourIsPositive, 5:fiveIsPositive, 6:sixIsPositive, 7:sevenIsPositive, 8:eightIsPositive, 9:nineIsPositive}
        return Numeral._positiveStmts[self.n]

class NumeralSequence(Operation):
    """
    Base class of BinarySequence, DecimalSequence, and HexSequence.
    """
    def __init__(self, operator, *digits):
        Operation.__init__(self, operator, digits)
        if len(digits) <= 1:
            raise Exception('A NumeralSequence should have two or more digits.  Single digit number should be represented as the corresponding Literal.')
        self.digits = digits
    
    def _formatted(self, formatType, **kwargs):
        return ''.join(digit.formatted(formatType) for digit in self.digits)

def isLiteralInt(expr):
    from proveit.number import Neg
    if isinstance(expr, Numeral):
        return True
    elif isinstance(expr, NumeralSequence):
        return True
    elif isinstance(expr, Neg) and isLiteralInt(expr.operand):
        return True
    return False        