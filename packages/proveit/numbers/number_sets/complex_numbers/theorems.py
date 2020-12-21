from proveit.logic import Forall, InSet, NotEquals
from proveit.numbers import Complex
from proveit.common import a
from proveit.numbers.common import zero, i, ComplexSansZero
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

i_in_complex = InSet(i, Complex)
i_in_complex

i_not_zero = NotEquals(i, zero)
i_not_zero

in_complex_sans_zero = Forall(a, InSet(a, ComplexSansZero),
                              domain=Complex, conditions=[NotEquals(a, zero)])
in_complex_sans_zero

end_theorems(locals(), __package__)
