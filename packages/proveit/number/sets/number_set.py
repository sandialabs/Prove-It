from proveit import Literal, ProofFailure, USE_DEFAULTS
from proveit.logic import InSet, Membership

class NumberSet(Literal):
    def __init__(self, string, latex, context):
        Literal.__init__(self, string, latex, context=context)
    
    def membershipObject(self, element):
        return NumberMembership(element, self)

class NumberMembership(Membership):
    def __init__(self, element, number_set):
        Membership.__init__(self, element)
        self.number_set = number_set

    def sideEffects(self, knownTruth):
        '''
        TODO
        '''
        return
        yield
        
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the number set under the given assumptions.
        '''   
        if hasattr(self.element, 'deduceInNumberSet'):
            return self.element.deduceInNumberSet(self.number_set, assumptions=assumptions)
        raise ProofFailure(InSet(self.element, self.number_set), assumptions, str(self.element) + " has no 'deduceInNumberSet' method.")

