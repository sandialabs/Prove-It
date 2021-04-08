from proveit import Function, Literal


class Distinct(Function):
    '''
    The Distinct operation defines a property for any collection.
    It evaluates to True iff the elements are all unique;
    that is, any pair of the given elements are not equal to each other.
    '''
    _operator_ = Literal('distinct', r'\textrm{distinct}', theory=__file__)

    def __init__(self, *elements, styles=None):
        Function.__init__(self, Distinct._operator_, elements,
                          styles=styles)
