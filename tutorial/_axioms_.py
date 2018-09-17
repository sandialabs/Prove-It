import sys
from proveit._core_.context import Context, Axioms
sys.modules[__name__] = Axioms(Context(__file__))
