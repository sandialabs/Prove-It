from proveit.logic import Forall, InSet, NotEquals
from proveit.number import Complex
from proveit.common import a
from proveit.number.common import zero, i, ComplexSansZero
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

iInComplex = InSet(i, Complex)
iInComplex

iNotZero = NotEquals(i, zero)
iNotZero

inComplexSansZero = Forall(a, InSet(a, ComplexSansZero), 
                             domain=Complex, conditions=[NotEquals(a, zero)])
inComplexSansZero

endTheorems(locals(), __package__)
