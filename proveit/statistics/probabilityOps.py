from proveit.expression import Operation, Literal
from proveit.common import x, X

pkg = __package__

class Prob(Operation):
    def __init__(self, event, random_variable):
        Operation.__init__(self, PROB, [event, random_variable])
        self.event = event
        self.random_variable = random_variable
    
    def formatted(self, formatType, fence=False):
        formattedEvent = self.event.formatted(formatType, fence=False)
        formattedVar = self.random_variable.formatted(formatType, fence=False)
        return 'Pr_{' + formattedVar + '}['+formattedEvent+']'
    
    def deduceInInterval(self):
        from axioms import probBetweenZeroAndOne
        return probBetweenZeroAndOne.specialize({x:self.random_variable, X:self.event})
    
    def deduceInReals(self):
        from theorems import probInReals
        return probInReals.specialize({x:self.random_variable, X:self.event})

PROB = Literal(pkg, 'PROB', operationMaker = lambda operands : Prob(*operands))
