from proveit import Operation, Literal, USE_DEFAULTS
from proveit._common_ import S, a, b

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
    
    def extractDistinctElems(self, aVar=None, bVar=None, assumptions=USE_DEFAULTS):
        '''
        Assuming the cardinality of the domain can be proven to be >= 2,
        proves and returns that there exists distinct elements in that domain.
        '''
        from _theorems_ import distinctElemExistence
        if aVar is None: aVar = a
        if bVar is None: bVar = b
        return distinctElemExistence.specialize({S:self.domain, a:aVar, b:bVar}, assumptions=assumptions).deriveConclusion()