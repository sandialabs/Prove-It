'''
impliesLiteral.py

Creates the IMPLIES literal which is used in prove-it's internal logic.  
We do not define the Implies Operation class here.  The standard one is
defined in basiclogic.boolean.boolOps.  The formatMap and operationMaker
of IMPLIES should be set, as desired, where the Implies Operation is defined.
'''

from proveit.expression import Literal

IMPLIES = Literal(__package__, 'IMPLIES')
