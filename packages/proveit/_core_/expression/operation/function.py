from .operation import Operation


class Function(Operation):
    '''
    A Function is an Operation with a default format as a function:
    f(x), Q(x, y), etc.
    '''

    def __init__(self, operator, operand_or_operands, styles=None):
        if styles is None:
            styles = dict()
        styles['operation'] = 'function'
        Operation.__init__(self, operator, operand_or_operands, styles=styles)
        if not hasattr(self, 'operator'):
            raise ValueError("A Function must be given a single `operator`. "
                             "%s is not a valid `operator`." % str(operator))


def function(operator, operand_or_operands):
    return Operation(operator, operand_or_operands,
                     {'operation': 'function'})
