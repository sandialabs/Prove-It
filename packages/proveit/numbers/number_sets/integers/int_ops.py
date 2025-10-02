from proveit import Operation, Literal

class Add(Operation):
    '''
    This defines Add for the purposes of defining Integers only.
    The default, general Add is defined in proveit.numbers.additions.
    '''

    # operator of the Add operation FOR NATURAL NUMBERS ONLY
    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        r'''
        Add together any number of operands.
        '''
        Operation.__init__(self, Add._operator_, operands, 
                           styles=styles)
        self.terms = self.operands

class Neg(Operation):
    '''
    This defines Neg for the purposes of defining Integers only.
    The default, general Neg is defined in proveit.numbers.negation.
    '''

    # operator of the Add operation FOR INTEGERS ONLY
    _operator_ = Literal(string_format='-', theory=__file__)
    
    def __init__(self, operand, styles=None):
        r'''
        Negate an operand.
        '''
        Operation.__init__(self, Neg._operator_, operand, 
                           styles=styles)
