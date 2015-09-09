from proveit.expression import Operation, Literal

pkg = __package__

# Special Unitary group
class SU(Operation):
    def __init__(self, n):
        '''
        Create some SU(n), the special unitary of degree n.
        '''
        Operation.__init__(self, SPECIAL_UNITARY, n)
        self.operand = n
        
SPECIAL_UNITARY = Literal(pkg, 'SU', operationMaker = lambda operands : SU(*operands))
