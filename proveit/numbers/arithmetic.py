import sys
from proveit.statement import *
from proveit.context import Context
from proveit.basiclogic.genericOperations import AssociativeOperation, BinaryOperation
from variables import a, b, cStar

literals = Literals()
literals.add('ADD')
literals.add('SUBTRACT')
literals.add('MULTIPY')
literals.add('DIVIDE'
literals.add('FRACTION')
literals.add('EXPONENTIATE')
literals.add('SUMMATION')
literals.add('PRODUCT')

def _defineAxioms():  
    # Composition of multi-Add, bypassing associativity for notational convenience:
    # forall_{a, b, c**} a + b + c** = a + (b + c**)
    _firstAxiom =\
    addComposition = Forall((a, b, cStar), Equals(Add(a, b, cStar), Add(a, Add(b, cStar))))
  
    return _firstAxiom, locals()

def _defineTheorems():
    return None

arithmetic = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)

class Add(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        AssociativeOperation.__init__(self, ADD, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        return '+'

class Divide(BinaryOperation):
    def __init__(self, *operands):
        r'''
        Divide two operands.
        '''
        BinaryOperation.__init__(self, DIVIDE, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
             return r'/'
        elif formatType == LATEX:
             return r'\div'

class Fraction(BinaryOperation):
    def __init__(self, *operands):
        r'''
        Divide two operands in fraction form.
        '''
        BinaryOperation.__init__(self, FRACTION, *operands)

    def formatted(self, formatType, fenced=False, subLeftFenced=True, subRightFenced=True):
        # override this default as desired
        pass
