from proveit import Function, Literal, USE_DEFAULTS
from proveit import S, a, b, x, N


class Card(Function):
    # operator of the Card operation
    _operator_ = Literal(string_format='card',
                         latex_format=r'\textrm{card}', theory=__file__)

    def __init__(self, domain):
        Function.__init__(self, Card._operator_, domain)
        self.domain = self.operands[0]

    def string(self, fence=False):
        return '|' + self.domain.string(fence=False) + '|'

    def latex(self, fence=False):
        return '|' + self.domain.latex(fence=False) + '|'

    def distinct_subset_existence(self, elems, assumptions=USE_DEFAULTS):
        '''
        Assuming the cardinality of the domain can be proven to be >= 2,
        proves and returns that there exists distinct elements in that domain.
        '''
        from . import distinct_subset_existence, distinct_pair_existence
        from proveit import composite_expression
        elems = composite_expression(elems)
        if elems.is_double():
            a_var, b_var = elems
            return distinct_pair_existence.instantiate(
                {S: self.domain, a: a_var, b: b_var}, assumptions=assumptions)
        else:
            _x = elems
            _N = _x.num_elements(assumptions)
            return distinct_subset_existence.instantiate(
                {S: self.domain, N: _N, x: _x}, assumptions=assumptions)
