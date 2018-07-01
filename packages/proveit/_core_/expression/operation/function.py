from operation import Operation

class Function(Operation):
    '''
    A Function is an Operation with a default format as a function:
    f(x), Q(x, y), etc.
    '''
    
    def __init__(self, operator, operand_or_operands, styles=dict(), requirements=tuple()):
        styles['operation']='function'
        Operation.__init__(self, operator, operand_or_operands, styles=styles, requirements=requirements)
