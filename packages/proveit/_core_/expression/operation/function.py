from proveit.decorators import equality_prover
from .operation import Operation


class Function(Operation):
    '''
    A Function is an Operation that will format as a function:
    f(x), Q(x, y), etc.
    The StyleOptions will not include 'operation' which will for
    Operation into a 'function' style rather than 'infix'.
    '''

    def __init__(self, operator, operand_or_operands=None, *, 
                 operands=None, styles=None):
        Operation.__init__(self, operator, operand_or_operands,
                           operands=operands, styles=styles)

    def style_options(self):
        '''
        Return the StyleOptions object for the Function.
        '''
        # We won't have the 'operation' style.  By doing so,
        # Operation will format with the operation:'function' style.
        options = Operation.style_options(self)
        first = options.options.pop(0)
        assert first[0]=='operation'
        return options

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False, 
                               **defaults_config):
        '''
        For a generic Function expression (e.g., "f(x)"), there is
        no evaluation strategy.
        '''
        from proveit.logic import EvaluationError
        if must_evaluate:
            raise EvaluationError(self)
        return Operation.shallow_simplification(self)
