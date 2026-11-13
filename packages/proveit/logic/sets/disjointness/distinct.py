from proveit import Function, Literal


class Distinct(Function):
    '''
    The Distinct operation defines a property for any collection.
    It evaluates to True iff the elements are all unique;
    that is, any pair of the given elements are not equal to each other.
    '''
    _operator_ = Literal('distinct', r'\textrm{distinct}', theory=__file__)

    def __init__(self, *elements, styles=None):
        Function.__init__(self, Distinct._operator_, elements,
                          styles=styles)


class AllDistinct(Function):
    '''
    AllDistinct(S) represents the claim that all elements of collection
    S are distinct --- i.e.,

        for all e_i, e_j in S, i != j => e_i != e_j.

    For example, AllDistinct({1, 2, 3}) is True, while
    AllDistinct({1, 2, 2}) is False. The argument S could be abstract
    (a variable), or S could be a tuple, list, Set, or ExprTuple.
    This is different from the Distinct() class defined further above,
    which accepts a variable number of arguments, each of which is
    an 'item' to be compared to the other arguments.

    '''

    _operator_ = Literal('AllDistinct', r'\textrm{AllDistinct}',
                         theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Initialize AllDistinct(S), the claim that all elements of S
        are distinct.
        '''

        super().__init__(AllDistinct._operator_, S, styles=styles)
        self.set = S

    def _function_formatted(self, format_type, **kwargs):
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        formatted_operator = self.operator.formatted(format_type, fence=True)
        lparen = r'\left(' if format_type=='latex' else '('
        rparen = r'\right)' if format_type=='latex' else ')'
        if (hasattr(self, 'operand') and 
                not isinstance(self.operand, ExprTuple)):
            formatted_operand = self.operand.formatted(
                    format_type, fence=True) # prev False
        else:
            formatted_operand = self.operands.formatted(
                    format_type, fence=True, sub_fence=False) # prev both False

        return (formatted_operator + lparen + formatted_operand + rparen)
