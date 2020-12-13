from proveit import Literal, OperationOverInstances
from proveit.numbers.number_sets import Interval, infinity, Real, IntervalCC
from proveit.numbers.negation import Neg

class Integrate(OperationOverInstances):
    # operator of the Integrate operation.
    _operator_ = Literal(stringFormat='Integrate', latexFormat=r'\int', theory=__file__)    

#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
#    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, index, integrand, domain, *, condition=None,
                 conditions=None):
        r'''
        Integrates integrand over indices over domain.
        Arguments serve analogous roles to Forall arguments (found in basiclogic.booleanss):
        index: single instance var
        integrand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(
                self, Integrate._operator_, index, integrand, 
                domain=domain, condition=condition, conditions=conditions)
        if len(self.instanceVars) != 1:
            raise ValueError('Only one index allowed per integral!')
        elif isinstance(self.domain,Interval):
            raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        elif self.domain == Real:
            self.domain = IntervalCC(Neg(infinity),infinity)
        self.index = self.instanceVars[0]
        self.integrand = self.instanceExpr
    
    def _closureTheorem(self, numberSet):
        from . import theorems
        #import complex.theorems
        if numberSet == Real:
            return theorems.integrationClosure
        #if numberSet == Complex:
        #    return complex.theorems.integrationClosure

        
    def formatted(self, formatType, fence=False):
#        if isinstance(self.domain,IntervalOO) or isinstance(self.domain,IntervalOC) or isinstance(self.domain,IntervalCO) or isinstance(self.domain,IntervalOO):
        if isinstance(self.domain,IntervalCC):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            return self.operator.formatted(formatType)+r'_{'+lower+r'}'+r'^{'+upper+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)
#        elif self.domain

        return self.operator.formatted(formatType)+r'_{'+self.domain.formatted(formatType)+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)

