from proveit.expression import Operation, Literal, STRING, LATEX

pkg = __package__

class ExprListCount(Operation):
    def __init__(self, *operands):
        Operation.__init__(self, EXPR_LIST_COUNT, operands)

EXPR_LIST_COUNT = Literal(pkg, 'EXPR_LIST_COUNT', {STRING:'#', LATEX:r'\#'}, operationMaker = lambda operands : ExprListCount(*operands))
