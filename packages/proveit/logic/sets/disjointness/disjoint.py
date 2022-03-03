from proveit import Function, Literal, prover

class Disjoint(Function):
    '''
    The Disjoint operation defines a property for a collection of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of any two of the sets is the empty set.
    We define this property to be True when given zero or one set
    (there are no pairs of sets, so all pairs are vacuously disjoint).
    '''
    _operator_ = Literal('disjoint', r'\textrm{disjoint}', theory=__file__)

    def __init__(self, *sets, styles=None):
        Function.__init__(self, Disjoint._operator_, sets,
                          styles=styles)
        self.sets = self.operands

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude that sets are Disjoint.  One of the sets must have
        a 'deduce_disjointness' method for this to work.
        '''
        for operand in self.sets:
            if hasattr(operand, 'deduce_disjointness'):
                return operand.deduce_disjointness(self)
        raise NotImplementedError(
                "Cannot conclude %s; non of the sets have a "
                "'deduce_disjointness' method."%self)
