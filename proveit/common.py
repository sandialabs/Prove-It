'''
common.py

Commonly used Variables and simple expressions involving them.
'''

from proveit.expression import Variable, Operation, LATEX
from proveit.multiExpression import MultiVariable, Etcetera

a = Variable('a')
b = Variable('b')
c = Variable('c')
d = Variable('d')
#e = Variable('e') # reserved for Euler's constant
f = Variable('f')
g = Variable('g')
h = Variable('h')
#i = Variable('i') # reserved for imaginary number
j = Variable('j')
k = Variable('k')
l = Variable('l')
m = Variable('m')
n = Variable('n')
o = Variable('o')
p = Variable('p')
q = Variable('q')
r = Variable('r')
s = Variable('s')
t = Variable('t')
u = Variable('u')
v = Variable('v')
w = Variable('w')
x = Variable('x')
y = Variable('y')
z = Variable('z')
A = Variable('A')
B = Variable('B')
C = Variable('C')
D = Variable('D')
N = Variable('N')
P = Variable('P')
Q = Variable('Q')
R = Variable('R')
S = Variable('S')
U = Variable('U')
X = Variable('X') 

Am = Operation(A,m)
Bm = Operation(B,m)
Cn = Operation(C,n)
PofA = Operation(P, A) # P(A)
Px = Operation(P, x) # P(x)
Py = Operation(P, y) # P(y)
Pxy = Operation(P, (x, y)) # P(x, y)
Pq = Operation(P, q) # P(q)
Qx = Operation(Q, x) # Q(x)
Qy = Operation(Q, y) # Q(x)
Ry = Operation(R, y) # R(y)
fa = Operation(f, a) # f(a)
fb = Operation(f, b) # f(b)
fab = Operation(f, (a, b)) # f(a, b)
fx = Operation(f, x) # f(x)
fy = Operation(f, y) # f(y)
fxy = Operation(f, (x, y)) # f(x, y)
gx = Operation(g, x) # g(x)
gy = Operation(g, y) # g(y)

alpha = Variable('alpha', {LATEX:r'\alpha'})
beta = Variable('beta', {LATEX:r'\beta'})
theta = Variable('theta', {LATEX:r'\theta'})
eps = Variable('eps',{LATEX:r'\varepsilon'})
Psi = Variable('Psi',{LATEX:r'\Psi'})
Upsilon = Variable('Upsilon',{LATEX:r'\Upsilon'})
Omega = Variable('Omega', {LATEX:r'\Omega'})

def etcMultiVar(var):
    return Etcetera(MultiVariable(var))

aEtc = etcMultiVar(a) # ..a..
bEtc = etcMultiVar(b) # ..b..
cEtc = etcMultiVar(c) # ..c..
Aetc = etcMultiVar(A) # ..A..
Cetc = etcMultiVar(C) # ..C..
Qetc = etcMultiVar(Q) # ..Q..
Retc = etcMultiVar(R) # ..R..
vEtc = etcMultiVar(v) # ..v..
xEtc = etcMultiVar(x) # ..x..
yEtc = etcMultiVar(y) # ..y..
zEtc = etcMultiVar(z) # ..z..
wEtc = etcMultiVar(w) # ..z..
fxEtc = Operation(f, xEtc) # f(..x..)
fyEtc = Operation(f, yEtc) # f(..y..)
fzEtc = Operation(f, zEtc) # f(..z..)
gxEtc = Operation(g, xEtc) # g(..x..)
gyEtc = Operation(g, yEtc) # g(..y..)
gzEtc = Operation(g, zEtc) # g(..z..)
PxEtc = Operation(P, xEtc) # P(..x..)
PyEtc = Operation(P, yEtc) # P(..y..)
PxyEtc = Operation(P, (xEtc, yEtc)) # P(..x.., ..y..)
etc_QxEtc = Etcetera(Operation(MultiVariable(Q), xEtc)) # ..Q(..x..)..
etc_QyEtc = Etcetera(Operation(MultiVariable(Q), yEtc)) # ..Q(..y..)..
etc_QzEtc = Etcetera(Operation(MultiVariable(Q), zEtc)) # ..Q(..z..)..
etc_RyEtc = Etcetera(Operation(MultiVariable(R), yEtc)) # ..R(..y..)..
