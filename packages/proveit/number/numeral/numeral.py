from proveit import Literal, Operation
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

    def buildArguments(self):
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
     
    def deduceInNaturals(self):
        if DigitLiteral._inNaturalsStmts is None:
            from natural.axioms import zeroInNaturals
            from natural.theorems import oneInNaturals, twoInNaturals, threeInNaturals, fourInNaturals, fiveInNaturals
            from natural.theorems import sixInNaturals, sevenInNaturals, eightInNaturals, nineInNaturals
            DigitLiteral._inNaturalsStmts = {0:zeroInNaturals, 1:oneInNaturals, 2:twoInNaturals, 3:threeInNaturals, 4:fourInNaturals, 5:fiveInNaturals, 6:sixInNaturals, 7:sevenInNaturals, 8:eightInNaturals, 9:nineInNaturals}
        return DigitLiteral._inNaturalsStmts[self.n]
    
    def deduceNotZero(self):
        if DigitLiteral._notZeroStmts is None:
            from natural.theorems import oneNotZero, twoNotZero, threeNotZero, fourNotZero, fiveNotZero
            from natural.theorems import sixNotZero, sevenNotZero, eightNotZero, nineNotZero
            DigitLiteral._notZeroStmts = {1:oneNotZero, 2:twoNotZero, 3:threeNotZero, 4:fourNotZero, 5:fiveNotZero, 6:sixNotZero, 7:sevenNotZero, 8:eightNotZero, 9:nineNotZero}
        return DigitLiteral._notZeroStmts[self.n]

    def deduceInNaturalsPos(self):
        if DigitLiteral._inNaturalsPosStmts is None:
            from natural.theorems import oneInNaturalsPos, twoInNaturalsPos, threeInNaturalsPos, fourInNaturalsPos, fiveInNaturalsPos
            from natural.theorems import sixInNaturalsPos, sevenInNaturalsPos, eightInNaturalsPos, nineInNaturalsPos
            DigitLiteral._inNaturalsPosStmts = {1:oneInNaturalsPos, 2:twoInNaturalsPos, 3:threeInNaturalsPos, 4:fourInNaturalsPos, 5:fiveInNaturalsPos, 6:sixInNaturalsPos, 7:sevenInNaturalsPos, 8:eightInNaturalsPos, 9:nineInNaturalsPos}
        return DigitLiteral._inNaturalsPosStmts[self.n]    

    def deducePositive(self):
        if DigitLiteral._positiveStmts is None:
            from natural.theorems import oneIsPositive, twoIsPositive, threeIsPositive, fourIsPositive, fiveIsPositive
            from natural.theorems import sixIsPositive, sevenIsPositive, eightIsPositive, nineIsPositive
            DigitLiteral._positiveStmts = {1:oneIsPositive, 2:twoIsPositive, 3:threeIsPositive, 4:fourIsPositive, 5:fiveIsPositive, 6:sixIsPositive, 7:sevenIsPositive, 8:eightIsPositive, 9:nineIsPositive}
        return DigitLiteral._positiveStmts[self.n]

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