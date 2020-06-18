from proveit import Operation, Literal

# pkg = __package__

# Special Unitary group
class SU(Operation):
    '''
    '''

	  # the literal operator of the SU operation
    _operator_ = Literal(stringFormat='SU', context=__file__)


    def __init__(self, n):
        '''
        Create some SU(n), the special unitary of degree n.
        '''
        Operation.__init__(self, SU._operator_, n)
        # self.operand = n
        self.degree = n
        
# SPECIAL_UNITARY = Literal(pkg, 'SU', operationMaker = lambda operands : SU(*operands))
