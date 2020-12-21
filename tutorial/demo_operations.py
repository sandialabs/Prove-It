'''
Module that defines a Operations for demonstration
purposes in this tutorial.
'''

from proveit import Operation, Literal


class Factorial(Operation):
    # _operator_ is a special class variable name, defining specific literal operator of the Operation class.
    # It is not only used for default formatting but also when performing
    # substitutions for rebuilding expressions.
    _operator_ = Literal('!')

    def __init__(self, operand):
        # creates the Operation with FACTORIAL as the operator and the provided
        # operand as its only operand.
        Operation.__init__(
            self,
            Factorial._operator_,
            operand)  # initializes self.operand

    def string(self, **kwargs):  # should accept kwargs even when not used (e.g., 'fence')
        # the operand should be fenced (wrapped in parentheses) to prevent
        # ambiguity
        return self.operand.string(fence=True) + Factorial._operator_.string()

    def latex(self, **kwargs):  # should accept kwargs even when not used (e.g., 'fence')
        # the operand should be fenced (wrapped in parentheses) to prevent
        # ambiguity
        return self.operand.latex(fence=True) + Factorial._operator_.latex()


class Multiply(Operation):

    # This operator Literal has a LaTeX format that differs from the string
    # format.
    _operator_ = Literal('*', r'\times')

    def __init__(self, *operands):  # takes a list of arguments as the operands
        # creates the AssociativeOperation with TIMES as the operator and any
        # number of operands.
        Operation.__init__(self, Multiply._operator_, operands)

    # The default formatting will display the operator between the operands
