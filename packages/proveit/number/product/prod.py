from proveit import Literal, OperationOverInstances

PRODUCT = Literal(__package__,  r'Product', r'\prod')

class Prod(OperationOverInstances):
#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
#    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, indices, summand, domain, conditions = tuple()):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        indices: instance vars
        summand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(self, PRODUCT, indices, summand, domain=domain, conditions=conditions)
