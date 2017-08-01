from proveit import Literal

class DigitLiteral(Literal):
    _inNaturalsStmts = None # initializes when needed
    _inNaturalsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, n):
        assert n >= 0 and n < 10, 'Digits are 0 through 9'
        Literal.__init__(self, str(n), context=__file__)
        self.n = n

    def buildArguments(self):
        '''
        Yield the argument values that could be used to recreate this DigitLiteral.
        '''
        yield str(self.n)
        
    @staticmethod
    def makeLiteral(string_format, latex_format, context):
        '''
        Make the DigitLiteral that matches the core information.
        '''
        from proveit import Context
        assert context==Context(__file__), 'Expecting a different Context for a DigitLiteral'
        return DigitLiteral(int(string_format))
     
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
        