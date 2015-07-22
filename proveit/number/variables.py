from proveit.expression import Variable, Literal, LATEX, STRING, Operation

pkg = __package__

A = Variable('A')
B = Variable('B')

a = Variable('a')
b = Variable('b')
c = Variable('c')

m = Variable('m')
n = Variable('n')
r = Variable('r')
t = Variable('t')
eps = Variable('eps',{LATEX:r'\varepsilon'})
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

e = Literal(pkg,'e')
i = Literal(pkg,'i')
pi = Variable('pi',{LATEX:r'\pi'})

k = Variable('k')
l = Variable('l')

zero = Literal(pkg,'0')
one = Literal(pkg,'1')
two = Literal(pkg,'2')
infinity = Literal(pkg,'infinity',{LATEX:r'\infty'})
minusOne = Literal(pkg,'minusOne',{LATEX:r'-1'})
minusTwo = Literal(pkg,'minusTwo',{LATEX:r'-2'})

Z   = Literal(pkg,'Z',{LATEX:r'\mathbb{Z}'})
Zp  = Literal(pkg,'Z^+',{LATEX:r'\mathbb{Z}^+'})
R   = Literal(pkg,'R',{LATEX:r'\mathbb{R}'})
zeroToOne = Literal(pkg,'zeroToOne',{LATEX:r'[0,1]'})

x = Variable('x')
y = Variable('y')
z = Variable('z')

tFunc = Literal(pkg,'tFunc')
tFunc_n_eps = Operation(tFunc, (n, eps))

QPE = Literal(pkg,'QPE')
QPEfunc = Operation(QPE,(U,u,t))

Am = Operation(A,m)