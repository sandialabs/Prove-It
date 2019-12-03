from proveit import Literal, ProofFailure, USE_DEFAULTS
from proveit.logic import InSet, Membership

class NumberSet(Literal):
    def __init__(self, string, latex, context):
        Literal.__init__(self, string, latex, context=context)
    
    def membershipObject(self, element):
        return NumberMembership(element, self)
    
    def membershipSideEffects(self, knownTruth):
        '''
        Yield side-effects for when the given member is in this number
        set.  The default is to have no side-effects, but this
        can be adapted for the various NumberSet classes.
        '''
        return
        yield
        

class NumberMembership(Membership):
    def __init__(self, element, number_set):
        Membership.__init__(self, element)
        self.number_set = number_set

    def sideEffects(self, knownTruth):
        '''
        Yield side-effects for when the represented membership,
        that self.element is in self.number_set, is proven.
        '''
        number_set, element = self.number_set, self.element
        if not isinstance(knownTruth.expr, InSet):
            raise ValueError("Expecting the knownTruth of a NumberMembership "
                               "sideEffects call to be for an InSet expression.")
        if knownTruth.element != self.element:
            raise ValueError("NumberMembership.sideEffects called with a "
                               "knownTruth that is inconsistent w.r.t. the "
                               "element.")
        if knownTruth.domain != self.number_set:
            raise ValueError("NumberMembership.sideEffects called with a "
                               "knownTruth that is inconsistent w.r.t. the "
                               "domain.")
        for side_effect in number_set.membershipSideEffects(knownTruth):
            yield side_effect
        
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the number set under the given assumptions.
        '''   
        if hasattr(self.element, 'deduceInNumberSet'):
            return self.element.deduceInNumberSet(self.number_set, assumptions=assumptions)
        raise ProofFailure(InSet(self.element, self.number_set), assumptions, str(self.element) + " has no 'deduceInNumberSet' method.")

