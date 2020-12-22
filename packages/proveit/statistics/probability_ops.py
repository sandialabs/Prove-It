from proveit import Operation, Literal
from proveit import x, X

pkg = __package__


class Prob(Operation):
    '''
    Updated Sun 1/26/2020 by wdc: updating the __init__ and _formatted
    methods, import statements. deduce_in_interval and deduce_in_real
    methods untouched.
    '''
    # the literal operator of the Prob operation class
    _operator_ = Literal('PROB', theory=__file__)

    def __init__(self, event, random_variable):
        Operation.__init__(self, Prob._operator_, (event, random_variable))
        self.event = self.operands[0]
        self.random_variable = self.operands[1]

    def _formatted(self, format_type, fence=False):
        formatted_event = self.event.formatted(format_type, fence=False)
        formatted_var = self.random_variable.formatted(
            format_type, fence=False)
        return 'Pr_{' + formatted_var + '}[' + formatted_event + ']'

    def deduce_in_interval(self):
        from axioms import prob_between_zero_and_one
        return prob_between_zero_and_one.instantiate(
            {x: self.random_variable, X: self.event})

    def deduce_in_real(self):
        from theorems import prob_in_real
        return prob_in_real.instantiate(
            {x: self.random_variable, X: self.event})

# PROB = Literal(pkg, 'PROB', operation_maker = lambda operands : Prob(*operands))
