from proveit.expression import Operation
from proveit.multiExpression import Etcetera
from boolean.boolSet import TRUE, FALSE
from equality.eqOps import Equals
from variables import a, b, f, g, x, y, z, A, C, P, Q, R

PofA = Operation(P, A) # P(A)
PofTrue = Operation(P, TRUE) # P(TRUE)
PofFalse = Operation(P, FALSE) # P(TRUE)
Px = Operation(P, x) # P(x)
Py = Operation(P, y) # P(y)
Pxy = Operation(P, (x, y)) # P(x, y)
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
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)

etcA = Etcetera(A) # ..A..
etcC = Etcetera(C) # ..C..
etcQ = Etcetera(Q) # ..Q..
etcR = Etcetera(R) # ..R..
xEtc = Etcetera(x) # ..x..
yEtc = Etcetera(y) # ..y..
zEtc = Etcetera(z) # ..z..
PxEtc = Operation(P, xEtc) # P(..x..)
PyEtc = Operation(P, yEtc) # P(..y..)
PxyEtc = Operation(P, (xEtc, yEtc)) # P(..x.., ..y..)
etc_QxEtc = Etcetera(Operation(Q, xEtc)) # ..Q(..x..)..
etc_QyEtc = Etcetera(Operation(Q, yEtc)) # ..Q(..y..)..
etc_RyEtc = Etcetera(Operation(R, yEtc)) # ..R(..y..)..
