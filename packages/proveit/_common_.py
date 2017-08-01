import sys
from proveit._core_.context import Context, CommonExpressions
sys.modules[__name__] = CommonExpressions(__file__)
