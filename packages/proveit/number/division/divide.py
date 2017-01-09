from proveit import Literal, BinaryOperation

DIVIDE = Literal(__package__, r'/', r'\div')

class Divide(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        BinaryOperation.__init__(self, DIVIDE, operandA, operandB)

    @classmethod
    def operatorOfOperation(subClass):
        return DIVIDE

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.divideRealClosure
        elif numberSet == RealsPos:
            return theorems.divideRealPosClosure
        elif numberSet == Complexes:
            return theorems.divideComplexClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.divideNotEqZero
