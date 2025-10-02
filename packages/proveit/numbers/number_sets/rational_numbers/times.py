from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class Times(Operation):
    '''
    Multiplication of a rational by a natural number, used to defined the
    set of rationals.
    '''
    
    # operator of the (functional) Power operation
    _operator_ = Literal(string_format='*', latex_format=r'\times',  # '×'
                         theory=__file__)
    
    def __init__(self, rational, num, *, styles=None):
        Operation.__init__(self, Times._operator_, (rational, num),
                           styles=styles)
