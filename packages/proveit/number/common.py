from proveit import Operation
from proveit.number import Add
from proveit.common import k, m, n, P
from proveit.number.sets.integer.common import *

Pzero = Operation(P, zero)
Pn = Operation(P, n)
P_nAddOne = Operation(P, Add(n, one))
Pm = Operation(P, m)
P_mAddOne = Operation(P, Add(m, one))
Pk = Operation(P, k)
