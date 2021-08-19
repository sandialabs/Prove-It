from proveit import Operation, Function, Literal

class VecSpaces(Function):
    '''
    A VecSpaces expression denotes the class of vector spaces
    over a particular field for the VecAdd and ScalarMult operations.
    
    The VecSpaces definition will enforce the operand to be a field
    in order to contain any members (or even define membership).
    This will allow us to use VecSpaces without an explicit constraint
    on its 'field' operand.
    '''
    
    _operator_ = Literal(
            string_format=r'VecSpaces', latex_format=r'\textrm{VecSpaces}',
            theory=__file__)
    
    def __init__(self, field, *, styles=None):
        Function.__init__(self, VecSpaces._operator_, field, styles=styles)
