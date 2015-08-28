from proveit.expression import Operation, Literal

pkg = __package__

class Prob(Operation):
    def __init__(self, A):
        Operation.__init__(self, PROB, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        return 'Pr['+self.operand.formatted(formatType, fence=True)+']'

PROB = Literal(pkg, 'PROB', operationMaker = lambda operands : Prob(*operands))
