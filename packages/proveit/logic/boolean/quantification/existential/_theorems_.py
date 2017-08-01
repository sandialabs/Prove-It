import sys
from proveit._core_.context import Context, Theorems
sys.modules[__name__] = Theorems(__file__)
