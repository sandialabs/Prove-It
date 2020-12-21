from proveit import ExpressionList
from proveit.logic import Forall, InSet, Iff, Equals, Implies, SubsetEq, And, SetOfAll, Union
from proveit.numbers import Natural, NaturalPos, Neg, Integer
from proveit.numbers import Add, GreaterThanEquals
from proveit.numbers import Len
from proveit.common import n, x_multi, x_etc, x, y, S
from .common import zero, one, two
from proveit import begin_axioms, end_axioms

begin_axioms(locals())

# Define the set of Natural as, essentially, the minimum set that contains zero and all of its successors;
# that is, n is in Natural iff n is in all sets that contain zero and all
# successors.
naturals_def = Forall(n, Equals(InSet(n, Natural), Forall(S, Implies(
    And(InSet(zero, S), Forall(x, InSet(Add(x, one), S), domain=S)), InSet(n, S)))))

# Define the length of an ExpressionList inductively.
expr_list_length_def = And(Equals(Len(), zero), Forall(
    (x_multi, y), Equals(Len(x_etc, y), Add(Len(x_etc), one))))

naturals_pos_def = Forall(
    n, Iff(
        InSet(
            n, NaturalPos), GreaterThanEquals(
                n, one)), domain=Natural)
naturals_pos_def

integers_def = Equals(
    Integer,
    Union(
        Natural,
        SetOfAll(
            n,
            Neg(n),
            domain=Natural)))


end_axioms(locals(), __package__)
