from proveit import Function, Operation, Literal
from proveit import x, X

pkg = __package__


class Prob(Function):
    '''
    Updated Sun 1/26/2020 by wdc: updating the __init__ and _formatted
    methods, import statements. deduce_in_interval and deduce_in_real
    methods untouched.
    '''
    # the literal operator of the Prob operation class
    _operator_ = Literal('Pr', latex_format=r'\textrm{Pr}', theory=__file__)

    def __init__(self, event, *, styles=None):
        Function.__init__(self, Prob._operator_, event, styles=styles)
        self.event = self.operand
