from proveit import Function, Literal

class Disjoint(Function):
    '''
    The Disjoint operation defines a property for a collection of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of any two of the sets is the empty set.
    We define this property to be True when given zero or one set
    (there are no pairs of sets, so all pairs are vacuously disjoint).
    '''
    _operator_ = Literal('disjoint', r'{\rm disjoint}', context=__file__)
    
    def __init__(self, *sets):
        Function.__init__(self, Disjoint._operator_, sets)

    