from proveit.expression import Variable, Literal, LATEX, STRING, Operation
from proveit.multiExpression import Etcetera
from proveit.number import Multiply
from proveit.common import *
from proveit.number.number import *
from proveit.number.numberSets import *
from proveit.basiclogic import Difference, Singleton

pkg = __package__

two_pi = Multiply(two, pi)

ComplexesSansZero = Difference(Complexes, Singleton(zero))

MonDecFuncs = Literal(__package__,'MonDecFuncs')
EvenFuncs = Literal(__package__,'EvenFuncs')
Funcs = Literal(__package__,'Funcs')


