from proveit import Function, Literal, prover

class Disjoint(Function):
    '''
    The Disjoint operation defines a property for a collection of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of any two of the sets is the empty set.
    We define this property to be True when given zero or one set
    (there are no pairs of sets, so all pairs are vacuously disjoint).
    '''
    _operator_ = Literal('disjoint', r'\textrm{disjoint}', theory=__file__)

    def __init__(self, *sets, styles=None):
        Function.__init__(self, Disjoint._operator_, sets,
                          styles=styles)
        self.sets = self.operands

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude that sets are Disjoint.  One of the sets must have
        a 'deduce_disjointness' method for this to work.
        '''
        for operand in self.sets:
            if hasattr(operand, 'deduce_disjointness'):
                return operand.deduce_disjointness(self)
        raise NotImplementedError(
                "Cannot conclude %s; non of the sets have a "
                "'deduce_disjointness' method."%self)


class AllDisjoint(Function):
    '''
    AllDisjoint(S) represents the claim that all sets within a
    collection S of sets are disjoint. The "collection" of sets
    could be a tuple of sets (translated in Prove-It into an ExprTuple
    of sets) or a Prove-It Set of sets.
    It evaluates to True iff the sets are mutually/pairwise disjoint;
    that is, the intersection of every pair of the sets is the empty
    set. We define this property to be True when given zero or one set
    (there are no pairs of sets, so all distinct pairs are vacuously
    disjoint).
    '''
    _operator_ = Literal('AllDisjoint', r'\textrm{AllDisjoint}',
                         theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Initialize the claim that the contents of S are all
        disjoint: AllDisjoint(S)
        '''

        super().__init__(AllDisjoint._operator_, S, styles=styles)
        self.collection = S

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
