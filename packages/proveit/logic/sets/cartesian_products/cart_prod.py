from proveit import Operation, Literal

class CartProd(Operation):
    '''
    A CartProd represents the Cartesian product of sets to produce
    a new set.
    '''
    
    _operator_ = Literal(string_format='X', latex_format=r'\times',
                         theory=__file__)
    
    def __init__(self, *operands, styles=None):
        Operation.__init__(self, CartProd._operator_, operands, 
                           styles=styles)