from .composite import Composite
from .expr_tuple import ExprTuple
from proveit._core_.defaults import defaults, USE_DEFAULTS


class ExprArray(ExprTuple):
    '''
    An ExprArray is simply an ExprTuple of ExprTuples.
    '''
    def __init__(self, *expressions, styles=None):
        '''

        '''

    pass