from proveit import Operation, Literal

class Distinct(Operation):
    '''
    The Distinct operation defines a property for any collection.
    It evaluates to True iff the elements are all unique; 
    that is, any pair of the given elements are not equal to each other.
    '''
    _operator_ = Literal('distinct', r'{\rm distinct}', context=__file__)
    
    def __init__(self, *elements):
        Operation.__init__(self, Distinct._operator_, elements)

    