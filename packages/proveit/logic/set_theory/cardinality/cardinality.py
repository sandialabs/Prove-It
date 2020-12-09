from proveit import Function, Literal, USE_DEFAULTS
from proveit._common_ import S, a, b, N

class Card(Function):
    # operator of the Card operation
    _operator_ = Literal(stringFormat='card', 
                         latexFormat=r'\textrm{card}', theory=__file__)

    def __init__(self, domain):
        Function.__init__(self, Card._operator_, domain)
        self.domain = self.operands[0]
    
    def string(self, fence=False):
        return '|' + self.domain.string(fence=False) + '|'
    
    def latex(self, fence=False):
        return '|' + self.domain.latex(fence=False) + '|'
    
    def distinctSubsetExistence(self, elems=None, assumptions=USE_DEFAULTS):
        '''
        Assuming the cardinality of the domain can be proven to be >= 2,
        proves and returns that there exists distinct elements in that domain.
        '''
        from proveit.numbers import num
        from ._theorems_ import distinctSubsetExistence, distinctPairExistence
        if len(elems)==2:
            aVar, bVar = elems
            return distinctPairExistence.instantiate({S:self.domain, a:aVar, b:bVar}, assumptions=assumptions)
        else:
            return distinctSubsetExistence.instantiate({S:self.domain, N:num(len(elems)), xMulti:elems}, assumptions=assumptions)
