from proveit import Literal, OperationOverInstances
from proveit.numbers.number_sets import Interval, infinity, Real, IntervalCC
from proveit.numbers.negation import Neg

class Integrate(OperationOverInstances):
    # operator of the Integrate operation.
    _operator_ = Literal(string_format='Integrate', latex_format=r'\int', theory=__file__)    

#    def __init__(self, summand-instance_expression, indices-instance_vars, domains):
#    def __init__(self, instance_vars, instance_expr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, index, integrand, domain, *, condition=None,
                 conditions=None):
        r'''
        Integrates integrand over indices over domain.
        Arguments serve analogous roles to Forall arguments (found in basiclogic.booleanss):
        index: single instance var
        integrand: instance_expressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(
                self, Integrate._operator_, index, integrand, 
                domain=domain, condition=condition, conditions=conditions)
        if len(self.instance_vars) != 1:
            raise ValueError('Only one index allowed per integral!')
        elif isinstance(self.domain,Interval):
            raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        elif self.domain == Real:
            self.domain = IntervalCC(Neg(infinity),infinity)
        self.index = self.instance_vars[0]
        self.integrand = self.instance_expr
    
    def _closureTheorem(self, number_set):
        from . import theorems
        #import complex.theorems
        if number_set == Real:
            return theorems.integration_closure
        #if number_set == Complex:
        #    return complex.theorems.integration_closure

        
    def formatted(self, format_type, fence=False):
#        if isinstance(self.domain,IntervalOO) or isinstance(self.domain,IntervalOC) or isinstance(self.domain,IntervalCO) or isinstance(self.domain,IntervalOO):
        if isinstance(self.domain,IntervalCC):
            lower = self.domain.lower_bound.formatted(format_type)
            upper = self.domain.upper_bound.formatted(format_type)
            return self.operator.formatted(format_type)+r'_{'+lower+r'}'+r'^{'+upper+r'}'+self.integrand.formatted(format_type, fence=fence)+'d'+self.index.formatted(format_type)
#        elif self.domain

        return self.operator.formatted(format_type)+r'_{'+self.domain.formatted(format_type)+r'}'+self.integrand.formatted(format_type, fence=fence)+'d'+self.index.formatted(format_type)

