from proveit import Literal, ProofFailure, USE_DEFAULTS
from proveit.logic import InSet

class NumberSet(Literal):
    def __init__(self, string, latex, context):
        Literal.__init__(self, string, latex, context=context)
        
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the set of Complexes under the given assumptions.
        '''   
        if hasattr(element, 'deduceInNumberSet'):
            return element.deduceInNumberSet(self, assumptions=assumptions)
        raise ProofFailure(InSet(element, self), assumptions, str(element) + " has not 'deduceInNumberSet' method.")
