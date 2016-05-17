import sys
from proveit.expression import *
from proveit.context import *
from genericOperations import *
from proveit.common import *

# set theory related literals
literals = Literals()
LIST = literals.add('LIST')

def _defineAxioms():        
    return None

def _defineTheorems():
    return None
        
lists = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)

class List(Operation):
    '''
    Defines a list of items (expressions).  Unlike ExpressionList in the proveit core, this
    kind of List is nestable.
    '''
    
    def __init__(self, *items):
        Operation.__init__(self, LIST, items)

    def formatted(self, formatType, fenced=False):
        return '[' + self.etcExpr.formatted(formatType, fenced=False) + ']'

Operation.registerOperation(LIST, lambda operands : List(*operands))