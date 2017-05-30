from proveit import Operation, Literal, USE_DEFAULTS

class Card(Operation):
    # operator of the Card operation
    _operator_ = Literal(stringFormat='card', context=__file__)

    def __init__(self, domain):
        Operation.__init__(self, Card._operator_, domain)
        self.domain = self.operands[0]
    
    def string(self, fence=False):
        return '|' + self.domain.string(fence=False) + '|'
    
    def latex(self, fence=False):
        return '|' + self.domain.latex(fence=False) + '|'
    