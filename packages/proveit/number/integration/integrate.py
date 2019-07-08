from proveit import Literal, OperationOverInstances
from proveit.number.sets import Interval, infinity, Reals, IntervalCC
from proveit.number.negation import Neg

class Integrate(OperationOverInstances):
    # operator of the Integrate operation.
    _operator_ = Literal(stringFormat='Integrate', latexFormat=r'\int', context=__file__)    

#    def __init__(self, summand-instanceExpression, indices-instanceVar, domains):
#    def __init__(self, instanceVar, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, index, integrand, domain, conditions = tuple()):
        r'''
        Integrates integrand over indices over domain.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        index: single instance var
        integrand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(self, Integrate._operator_, index, integrand, domain=domain, conditions=conditions)
        if len(self.instanceVar) != 1:
            raise ValueError('Only one index allowed per integral!')
        elif isinstance(self.domain,Interval):
            raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        elif self.domain == Reals:
            self.domain = IntervalCC(Neg(infinity),infinity)
        self.index = self.instanceVar[0]
        self.integrand = self.instanceExpr
    
    def _closureTheorem(self, numberSet):
        from . import theorems
        #import complex.theorems
        if numberSet == Reals:
            return theorems.integrationClosure
        #if numberSet == Complexes:
        #    return complex.theorems.integrationClosure

        
    def formatted(self, formatType, fence=False):
#        if isinstance(self.domain,IntervalOO) or isinstance(self.domain,IntervalOC) or isinstance(self.domain,IntervalCO) or isinstance(self.domain,IntervalOO):
        if isinstance(self.domain,IntervalCC):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            return self.operator.formatted(formatType)+r'_{'+lower+r'}'+r'^{'+upper+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)
#        elif self.domain

        return self.operator.formatted(formatType)+r'_{'+self.domain.formatted(formatType)+r'}'+self.integrand.formatted(formatType, fence=fence)+'d'+self.index.formatted(formatType)

