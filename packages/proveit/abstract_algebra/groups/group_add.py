from proveit import Operation

class GroupAdd(Operation):
    '''
    Denote general addition over a tuple of elements of any group in 
    analogy to number addition.
    '''

    def __init__(self, operator, operands, *, styles=None):
        return Operation.__init__(self, operator, operands, styles=None)
