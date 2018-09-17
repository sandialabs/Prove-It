import sys
from proveit._core_.context import Theorems
sys.modules[__name__] = Theorems(__file__)
