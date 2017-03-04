'''
common.py

Commonly used Variables and simple expressions involving them.
'''

from proveit import Variable, Operation, MultiVariable, Etcetera

a = Variable('a')
b = Variable('b')
c = Variable('c')
d = Variable('d')
e = Variable('e') 
f = Variable('f')
g = Variable('g')
h = Variable('h')
i = Variable('i') 
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
E = Variable('E')
F = Variable('F')
G = Variable('G')
H = Variable('H')
I = Variable('I')
J = Variable('J')
K = Variable('K')
L = Variable('L')
M = Variable('M')
N = Variable('N')
O = Variable('O')
P = Variable('P')
Q = Variable('Q')
R = Variable('R')
S = Variable('S')
T = Variable('T')
U = Variable('U')
V = Variable('V')
W = Variable('W') 
X = Variable('X') 
Y = Variable('Y') 
Z = Variable('Z') 

Am = Operation(A,m)
Bm = Operation(B,m)
Cn = Operation(C,n)
PofA = Operation(P, A) # P(A)
Px = Operation(P, x) # P(x)
Py = Operation(P, y) # P(y)
Pxy = Operation(P, (x, y)) # P(x, y)
Pxyz = Operation(P, (x, y, z)) # P(x, y, z)
Pq = Operation(P, q) # P(q)
Qx = Operation(Q, x) # Q(x)
Qy = Operation(Q, y) # Q(x)
Rx = Operation(R, x) # R(x)
Ry = Operation(R, y) # R(y)
fa = Operation(f, a) # f(a)
fb = Operation(f, b) # f(b)
fab = Operation(f, (a, b)) # f(a, b)
fx = Operation(f, x) # f(x)
fy = Operation(f, y) # f(y)
fxy = Operation(f, (x, y)) # f(x, y)
gx = Operation(g, x) # g(x)
gy = Operation(g, y) # g(y)

alpha = Variable('alpha', r'\alpha')
beta = Variable('beta', r'\beta')
theta = Variable('theta', r'\theta')
eps = Variable('eps', r'\varepsilon')
Psi = Variable('Psi', r'\Psi')
Upsilon = Variable('Upsilon', r'\Upsilon')
Omega = Variable('Omega', r'\Omega')

def multiAndEtcVar(stringFormat, latexFormat=None):
    multiVar = MultiVariable(stringFormat, latexFormat)
    return multiVar, Etcetera(multiVar)

aMulti, aEtc = multiAndEtcVar('a') # ..a..
bMulti, bEtc = multiAndEtcVar('b') # ..b..
cMulti, cEtc = multiAndEtcVar('c') # ..c..
Amulti, Aetc = multiAndEtcVar('A') # ..A..
Bmulti, Betc = multiAndEtcVar('B') # ..B..
Cmulti, Cetc = multiAndEtcVar('C') # ..C..
Dmulti, Detc = multiAndEtcVar('D') # ..D..
Emulti, Eetc = multiAndEtcVar('E') # ..E..
Qmulti, Qetc = multiAndEtcVar('Q') # ..Q..
Rmulti, Retc = multiAndEtcVar('R') # ..R..
vMulti, vEtc = multiAndEtcVar('v') # ..v..
xMulti, xEtc = multiAndEtcVar('x') # ..x..
yMulti, yEtc = multiAndEtcVar('y') # ..y..
zMulti, zEtc = multiAndEtcVar('z') # ..z..
wMulti, wEtc = multiAndEtcVar('w') # ..z..
fxEtc = Operation(f, xEtc) # f(..x..)
fyEtc = Operation(f, yEtc) # f(..y..)
fzEtc = Operation(f, zEtc) # f(..z..)
gxEtc = Operation(g, xEtc) # g(..x..)
gyEtc = Operation(g, yEtc) # g(..y..)
gzEtc = Operation(g, zEtc) # g(..z..)
PxEtc = Operation(P, xEtc) # P(..x..)
PyEtc = Operation(P, yEtc) # P(..y..)
PxyEtc = Operation(P, (xEtc, yEtc)) # P(..x.., ..y..)
etc_Qx = Etcetera(Operation(MultiVariable('Q'), x)) # ..Q(x)..
etc_Qy = Etcetera(Operation(MultiVariable('Q'), y)) # ..Q(y)..
etc_QxEtc = Etcetera(Operation(MultiVariable('Q'), xEtc)) # ..Q(..x..)..
etc_QyEtc = Etcetera(Operation(MultiVariable('Q'), yEtc)) # ..Q(..y..)..
etc_QzEtc = Etcetera(Operation(MultiVariable('Q'), zEtc)) # ..Q(..z..)..
etc_RyEtc = Etcetera(Operation(MultiVariable('R'), yEtc)) # ..R(..y..)..
