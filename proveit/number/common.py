from proveit import Literal
from proveit.number import Mult, Complexes
from proveit.number.set.integer.common import zero, one, two, three, four, five, six, seven, eight, nine, num, infinity
from proveit.number.set.real.common import e, pi
from proveit.number.set.complex.common import i
from proveit.logic import Difference, Singleton

zero, one, two, three, four, five, six, seven, eight, nine, num, infinity
e, pi
i # imaginary number
two_pi = Mult(two, pi)

ComplexesSansZero = Difference(Complexes, Singleton(zero))

MonDecFuncs = Literal(__package__,'MonDecFuncs')
EvenFuncs = Literal(__package__,'EvenFuncs')
Funcs = Literal(__package__,'Funcs')


