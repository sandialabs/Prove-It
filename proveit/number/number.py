from proveit.expression import Literal, LATEX
from proveit.number.arithmeticOps import Neg
from proveit.number.natural.decimal import WholeDecimal

pkg = __package__

class DigitLiteral(Literal):
    _inNaturalsStmts = None # initializes when needed
    _inNaturalsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, n):
        assert n >= 0 and n < 10, 'Digits are 0 through 9'
        Literal.__init__(self, pkg, str(n))
        self.n = n
    
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
        
zero = DigitLiteral(0)
one = DigitLiteral(1)
two = DigitLiteral(2)
three = DigitLiteral(3)
four = DigitLiteral(4)
five = DigitLiteral(5)
six = DigitLiteral(6)
seven = DigitLiteral(7)
eight = DigitLiteral(8)
nine = DigitLiteral(9)

ALL_DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

infinity = Literal(pkg,'infinity',{LATEX:r'\infty'})
minusOne = Neg(one)
minusTwo = Neg(two)

def num(x):
    if x < 0:
        return Neg(num(abs(x)))
    if isinstance(x, int):
        if x < 10:
            if x == 0:
                return zero
            elif x == 1:
                return one
            elif x == 2:
                return two
            elif x == 3:
                return three
            elif x == 4:
                return four
            elif x == 5:
                return five
            elif x == 6:
                return six
            elif x == 7:
                return seven
            elif x == 8:
                return 8
            elif x == 9:
                return 9
        else:
            return WholeDecimal([num(int(digit)) for digit in str(x)])
    else:
        assert False, 'num not implemented for anything except integers currently. plans to take in strings or floats with specified precision'

class IrrationalLiteral(Literal):
    _inRealsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, name, formatMap = None):
        Literal.__init__(self, pkg, name, formatMap)
    
    def deduceInRealsPos(self):
        if IrrationalLiteral._inRealsPosStmts is None:
            from real.theorems import eInRealsPos, piInRealsPos
            IrrationalLiteral._inRealsPosStmts = {'e':eInRealsPos, 'pi':piInRealsPos}
        return IrrationalLiteral._inRealsPosStmts[self.name]

    def deduceNotZero(self):
        if IrrationalLiteral._notZeroStmts is None:
            from real.theorems import eNotZero, piNotZero
            IrrationalLiteral._notZeroStmts = {'e':eNotZero, 'pi':piNotZero}
        return IrrationalLiteral._notZeroStmts[self.name]
    
    def deducePositive(self):
        if IrrationalLiteral._positiveStmts is None:
            from real.theorems import eIsPositive, piIsPositive
            IrrationalLiteral._positiveStmts = {'e':eIsPositive, 'pi':piIsPositive}
        return IrrationalLiteral._positiveStmts[self.name]
    
e = IrrationalLiteral('e')
pi = IrrationalLiteral('pi',{LATEX:r'\pi'})

class ComplexLiteral(Literal):
    _inComplexesStmts = None # initializes when needed

    def __init__(self, name, formatMap = None):
        Literal.__init__(self, pkg, name, formatMap)
    
    def deduceInComplexes(self):
        if ComplexLiteral._inComplexesStmts is None:
            from complex.theorems import iInComplexes
            ComplexLiteral._inComplexesStmts = {'i':iInComplexes}
        return ComplexLiteral._inComplexesStmts[self.name]    

    def deduceNotZero(self):
        if ComplexLiteral._notZeroStmts is None:
            from complex.theorems import iNotZero
            ComplexLiteral._notZeroStmts = {'i':iNotZero}
        return ComplexLiteral._notZeroStmts[self.name]

i = ComplexLiteral('i')
