'''
Treats theorem/axiom dill in .pv_it to act as if they were
variables defined in this module through some Python trickery.
'''

import sys
from proveit.special_statement_retrieval import SpecialStatementRetrieval
sys.modules[__name__] = SpecialStatementRetrieval(__file__)
