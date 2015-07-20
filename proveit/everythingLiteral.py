'''
everythingLiteral.py

Creates the EVERYTHING literal which is used in prove-it's internal logic
(when a forall Operation has no domain restriction -- the EVERYTHING
domain is then used).
The formatMap of EVERYTHING should be set, as desired, where the In
Operation is defined.
'''

from proveit.expression import Literal

EVERYTHING = Literal(__package__, 'EVERYTHING')
