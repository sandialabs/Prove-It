'''
Module that defines a LambdaApplication Operation
class for demonstration purposes in this tutorial.
'''

from proveit import Operation, Literal, NamedExprs


class LambdaApplication(Operation):
    _operator_ = Literal('LAMBDA_APPLICATION', r'{\rm LAMBDA\_APPLICATION}')

    def __init__(self, lambda_fn, operand, *, styles=None):
        Operation.__init__(self, LambdaApplication._operator_, 
                           NamedExprs(('lambda_fn', lambda_fn), 
                                      ('operand', operand)),
                           styles=styles)
        # The operand of the Lambda function
        self.lambda_operand = self.operands['operand']

    @classmethod
    def extract_init_arg_value(operation_class, arg_name, operator, operand):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value as determined by the operator and
        operand of the LambdaApplication Operation.
        (This is important so that Prove-It knows how to 'make' an altered
        copy of this Operation).
        '''
        assert isinstance(
            operand, NamedExprs), "Expecting LambdaApplication operand to be a NamedExprs object"
        if arg_name == 'lambda_fn':
            return operand['lambda_fn']
        elif arg_name == 'operand':
            return operand['operand']

    def string(self, **kwargs):  # should accept kwargs even when not used (e.g., 'fence')
        return self.lambda_fn.string(
            fence=True) + '(' + self.lambda_operand.string() + ')'

    def latex(self, **kwargs):  # should accept kwargs even when not used (e.g., 'fence')
        return self.lambda_fn.latex(
            fence=True) + '(' + self.lambda_operand.latex() + ')'
