from proveit.logic import Forall, InSet, NotEquals
from proveit.number import Complexes
from proveit.common import a
from proveit.number.common import zero, i, ComplexesSansZero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

iInComplexes = InSet(i, Complexes)
iInComplexes

iNotZero = NotEquals(i, zero)
iNotZero

inComplexesSansZero = Forall(a, InSet(a, ComplexesSansZero), 
                             domain=Complexes, conditions=[NotEquals(a, zero)])
inComplexesSansZero

endTheorems(locals(), __package__)
