from proveit import Function, Literal, USE_DEFAULTS
from proveit._common_ import S, a, b, N, xx

class Card(Function):
    # operator of the Card operation
    _operator_ = Literal(stringFormat='card', context=__file__)

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
        from proveit.number import num
        from _theorems_ import distinctSubsetExistence, distinctPairExistence
        if len(elems)==2:
            aVar, bVar = elems
            return distinctPairExistence.specialize({S:self.domain}, relabelMap={a:aVar, b:bVar}, assumptions=assumptions)
        else:
            return distinctSubsetExistence.specialize({S:self.domain, N:num(len(elems))}, relabelMap={xMulti:elems}, assumptions=assumptions)
