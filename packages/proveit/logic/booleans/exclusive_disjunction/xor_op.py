from proveit import (
    equality_prover, Literal, Operation, SimplificationDirectives)
from proveit.logic.booleans import in_bool

class XOr(Operation):
    '''
    XOr(A, B) represents the logical exclusive or (denoted xor) on
    boolean operands A and B, evaluating to TRUE if and only if A is
    TRUE or B is TRUE but not both. Like the logical Or, XOr is both
    commutative and associative. There is a nice Wikipedia entry
    for XOR at https://en.wikipedia.org/wiki/Exclusive_or .
    This class is under construction by wdc beginning 20250417 using
    the logic/sets/booleans logical Or class as a model.
    '''

    # The operator of the XOr operation
    _operator_ = Literal(
            string_format='xor', latex_format=r'\oplus', theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            ungroup=True)

    # used to avoid infinite recursion inside of unary_reduction
    trivial_xors = set()

    def __init__(self, *operands, styles=None):
        '''
        XOr on any number of operands: A xor B xor ... xor Z
        '''
        Operation.__init__(self, XOr._operator_, operands, styles=styles)
        # deduce trivial disjunctive equivalances with 0 or 1 operand;
        # avoid infinite recursion by storing previously encountered
        # expressions
        if self in XOr.trivial_xors:
            return
        operands = self.operands
        if operands.num_entries() == 0:
            XOr.trivial_xors.add(self)
            try:
                from proveit.logic.booleans.exclusive_disjunction import (
                        empty_xor)
            except BaseException:
                # empty_xor not initially defined when
                # doing a clean rebuild
                pass
        if operands.is_single():
            operand = operands[0]
            try:
                XOr.trivial_xors.add(self)
                in_bool(operand).prove(automation=False)
                self.unary_reduction()
            except BaseException:
                pass


    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        '''
        For the degenerate case of XOr(A), where A is Boolean, derive
        and return |–[xor](A) = A. For example, calling
            XOr(A).unary_reduction([in_bool(A)])
        will return:
            {A in Bool} |– [xor](A) = A
        '''
        from proveit.logic.booleans.exclusive_disjunction import (
            unary_or_reduction)
        if not self.operands.is_single():
            raise ValueError(
                    "XOr.unary_reduction(): expression must have only a "
                    "single operand in order to invoke the "
                    "unary_or_reduction theorem.")
        operand = self.operands[0]
        return unary_or_reduction.instantiate({A: operand})
