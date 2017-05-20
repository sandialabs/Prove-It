import sys
from proveit._core_.context import Context, Theorems
sys.modules[__name__] = Theorems(Context(__file__))
