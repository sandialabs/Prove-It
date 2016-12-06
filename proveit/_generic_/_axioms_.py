from associative_operation import AssociativeOperation
from proveit import beginAxioms, endAxioms, Variable
from proveit.common import xEtc, y, P, PxEtc, S, n
from proveit.logic import Equals, Forall, And
from proveit.number import Add, zero, one
from length import Len

op = Variable('*', r'\cdot')


beginAxioms(locals())

lengthDef = And(Equals(Len(), zero), Forall((xEtc, y), Equals(Len(xEtc, y), Add(Len(xEtc), one))))

endAxioms(locals(), __package__)
