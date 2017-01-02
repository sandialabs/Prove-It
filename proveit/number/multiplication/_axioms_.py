from proveit.logic import Forall, Equals
from proveit.number import Mult
from proveit.number.common import one
from proveit.common import x, xEtc, yEtc, zEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# base case for composition with multiplicative identity
multEmpty = Equals(Mult(), one)
multEmpty

multComposition = Forall((x, yEtc), Equals(Mult(x, yEtc), Mult(x, Mult(yEtc))))
multComposition

endAxioms(locals(), __package__)

