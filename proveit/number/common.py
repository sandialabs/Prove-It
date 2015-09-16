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


#e = Variable('e')
phi = Variable('phi',{LATEX:r'\phi'})

U   = Variable('U')
#U   = Literal(pkg,'U')
#SUm = Variable('SU(m)')
SUm = Operation(U,m)
C2m = Variable('C^(2^m)',{LATEX:r'C^{2^m}'})

H = Literal(pkg,'H',{LATEX:r'\mathcal{H}'})
Hm = Operation(H,m)

u = Variable('ket_u',{LATEX:r'|u\rangle'})



theta = Variable('theta',{LATEX:r'\theta'})
delta = Variable('delta',{LATEX:r'\delta'})

tFunc = Literal(pkg,'tFunc')
tFunc_n_eps = Operation(tFunc, (n, eps))  
                  
QPE = Literal(pkg,'QPE')
QPEfunc = Operation(QPE,(U,u,t))

Am = Operation(A,m)
Bm = Operation(B,m)
Cn = Operation(C,n)

MonDecFuncs = Literal(__package__,'MonDecFuncs')
EvenFuncs = Literal(__package__,'EvenFuncs')
Funcs = Literal(__package__,'Funcs')


