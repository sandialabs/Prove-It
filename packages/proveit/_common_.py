import sys
from proveit._core_.context import Context, CommonExpressions
sys.modules[__name__] = CommonExpressions(Context(__file__))
