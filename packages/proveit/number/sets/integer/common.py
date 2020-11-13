from proveit import Literal
from proveit.number.sets.natural.naturals import NaturalsSet, NaturalsPosSet
from .integers import IntegerSet
from digit import DigitLiteral

Naturals = NaturalsSet()
NaturalsPos = NaturalsPosSet()
Integers = IntegerSet()

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

infinity = Literal('infinity',r'\infty', __file__)

