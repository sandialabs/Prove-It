'''
forallLiteral.py

Creates the FORALL literal which is used in prove-it's internal logic.  
We do not define the Forall Operation class here.  The standard one is
defined in basiclogic.boolean.quantifiers.  The formatMap and operationMaker
of FORALL should be set, as desired, where the Forall Operation is defined.
The operationMaker must take a single operand in the following proper form
('->' represents a Lambda and {...} represents an ExpressionDict):
      {'instance_mapping' : instanceVars -> {'expression':instanceExpr, 'condition':conditions}, 'domain':domain}
As an alternative, FORALL operationMaker must also be able to take the following named
parameters:  instanceVars, instanceExpr, conditions, domain.
'''

from proveit.expression import Literal

FORALL = Literal(__package__, 'FORALL')
