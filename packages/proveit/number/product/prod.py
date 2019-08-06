from proveit import Literal, OperationOverInstances

class Prod(OperationOverInstances):
    # operator of the Prod operation.
    _operator_ = Literal(stringFormat='Prod', latexFormat=r'prod', context=__file__)
    
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
        # nestMultiIvars=True will cause it to treat multiple instance variables as nested Prod operations internally
        # and only join them together as a style consequence.
        OperationOverInstances.__init__(self, Prod._operator_, indices, summand, domain=domain, conditions=conditions, nestMultiIvars=True)
