from proveit import Operation, Literal, USE_DEFAULTS

CARDINALITY = Literal(__package__, stringFormat = 'card')

class Card(Operation):
    def __init__(self, domain):
        Operation.__init__(self, CARDINALITY, domain)
        self.domain = self.operands[0]
        
    @classmethod
    def operatorOfOperation(subClass):
        return CARDINALITY

    def string(self, fence=False):
        return '|' + self.domain.string(fence=False) + '|'
    
    def latex(self, fence=False):
        return '|' + self.domain.latex(fence=False) + '|'
    