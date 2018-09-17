import sys
from proveit._core_.context import Axioms
sys.modules[__name__] = Axioms(__file__)
