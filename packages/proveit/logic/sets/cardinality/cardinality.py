from proveit import Function, Literal, USE_DEFAULTS, prover, equality_prover
from proveit import S, a, b, x, N


class Card(Function):
    # operator of the Card operation
    _operator_ = Literal(string_format='card',
                         latex_format=r'\textrm{card}', theory=__file__)

    def __init__(self, domain, *, styles=None):
        Function.__init__(self, Card._operator_, domain, styles=styles)
        self.domain = self.operands[0]

    def string(self, fence=False):
        return '|' + self.domain.string(fence=False) + '|'

    def latex(self, fence=False):
        return '|' + self.domain.latex(fence=False) + '|'

    @prover
    def distinct_subset_existence(self, elems, **defaults_config):
        '''
        Assuming the cardinality of the domain can be proven to be >= 2,
        proves and returns that there exists distinct elements in that 
        domain.
        '''
        from . import distinct_subset_existence, distinct_pair_existence
        from proveit import composite_expression
        elems = composite_expression(elems)
        if elems.is_double():
            a_var, b_var = elems
            return distinct_pair_existence.instantiate(
                {S: self.domain, a: a_var, b: b_var})
        else:
            _x = elems
            _N = _x.num_elements()
            return distinct_subset_existence.instantiate(
                {S: self.domain, N: _N, x: _x})

    @equality_prover("computed", "compute")
    def computation(self, **defaults_config):
        '''
        Prove the equality of this Card expression with an element of
        the cardinal numbers.  For the Card of a finite set, 
        it simply equates to the size.
        '''
        if hasattr(self.domain, 'deduce_cardinality'):
            return self.domain.deduce_cardinality()
        raise NotImplementedError(
                "Evaluation of the cardinality of %s is not implemented. "
                "%s.deduce_cardinality method is required."
                %(self.domain, self.domain.__class__))

    
    @equality_prover("evaluated", "evaluate")
    def evaluation(self, **defaults_config):
        '''
        Prove the equality of this Card expression with an
        irreducible cardinal number.  For the Card of a finite set, 
        it simply evaluates to the size.
        '''
        return self.computation.inner_expr().rhs.evaluate()
