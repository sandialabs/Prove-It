'''
Module that defines a LambdaApplication Operation
class for demonstration purposes in this tutorial.
'''

from proveit import Operation, Literal, NamedExprs

class LambdaApplication(Operation):
    _operator_ = Literal('LAMBDA_APPLICATION', r'{\rm LAMBDA\_APPLICATION}')
    
    def __init__(self, lambdaFn, operand):
        Operation.__init__(self, LambdaApplication._operator_, NamedExprs([('lambdaFn',lambdaFn), ('operand',operand)]))
        self.lambdaFn = self.operands['lambdaFn'] # The Lambda function operand
        self.lambdaOperand = self.operands['operand'] # The operand of the Lambda function
    
    def string(self, **kwargs): # should accept kwargs even when not used (e.g., 'fence')
        return self.lambdaFn.string(fence=True) + '(' + self.lambdaOperand.string() + ')'
    
    def latex(self, **kwargs): # should accept kwargs even when not used (e.g., 'fence')
        return self.lambdaFn.latex(fence=True) + '(' + self.lambdaOperand.latex() + ')'
