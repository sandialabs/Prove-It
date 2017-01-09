from proveit import Literal, BinaryOperation

DIFFERENCE = Literal(__package__, '-')

class Difference(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, DIFFERENCE, A, B)

    @classmethod
    def operatorOfOperation(subClass):
        return DIFFERENCE
