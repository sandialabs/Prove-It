from proveit.basiclogic import *
from proveit.numberss import *

m = Variable('m')
n = Variable('n')
t = Variable('t')
eps = Variable('eps',{LATEX:r'\varepsilon'})
e = Variable('e')
phi = Variable('phi',{LATEX:r'\phi'})

pi = Variable('pi',{LATEX:r'\pi'})
i = Variable('i')
one = Variable('1')
two = Variable('2')
minusOne = Variable('minusOne',{LATEX:r'-1'})

Zp  = Variable('Z^+',{LATEX:r'\mathbb{Z}^+'})
U   = Variable('U')
SUm = Variable('SU(m)')
C2m = Variable('C^(2^m)',{LATEX:r'C^{2^m}'})

u = Variable('ket_u',{LATEX:r'|u\rangle'})
#u = Variable('ket_u')

zeroToOne = Variable('zeroToOne',{LATEX:r'[0,1]'})

tFunc = Variable('tFunc')
tFunc_n_eps = Operation(tFunc, (n, eps))

QPE = Variable('QPE')
QPEfunc = Operation(QPE,(U,u,t))


#Forall_{m, n, t in Z+, e in [0, 1]   |   t = n + ceil[log_2(2 + 1 / (2 e)]}
# Forall_{U in SU(m), u in H^{2^m}, rho in [0, 1]   |   U |u> = e^{2 pi i rho} |u>}
#  Pr[ |QPE(U, u, t) - rho| <= 1 / 2^n] >= 1 - e
