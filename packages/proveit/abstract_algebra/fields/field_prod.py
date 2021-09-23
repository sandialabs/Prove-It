from proveit.abstract_algebra import GroupSum

class FieldProd(GroupSum):
    '''
    Denote general product over a set of elements of any field in 
    analogy to a number product.  We regard this as a GroupSum
    since any field (minus zero) is a group under multplication.
    For the most part, standard group summation rules apply; there
    are additional rules here to deal with multiplication by zero.
    '''
    
    def __init__(self, operator, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, operator, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)
