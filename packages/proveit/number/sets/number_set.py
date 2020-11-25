from proveit import Literal, ProofFailure, defaults, USE_DEFAULTS
from proveit.logic import Equals, InSet, Membership

class NumberSet(Literal):
    def __init__(self, string, latex, context):
        Literal.__init__(self, string, latex, context=context)
    
    def membershipObject(self, element):
        return NumberMembership(element, self)
    
    def membershipSideEffects(self, judgment):
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

    def sideEffects(self, judgment):
        '''
        Yield side-effects for when the represented membership,
        that self.element is in self.number_set, is proven.
        '''
        number_set, element = self.number_set, self.element
        if not isinstance(judgment.expr, InSet):
            raise ValueError("Expecting the judgment of a NumberMembership "
                               "sideEffects call to be for an InSet expression.")
        if judgment.element != element:
            raise ValueError("NumberMembership.sideEffects called with a "
                               "judgment that is inconsistent w.r.t. the "
                               "element.")
        if judgment.domain != number_set:
            raise ValueError("NumberMembership.sideEffects called with a "
                               "judgment that is inconsistent w.r.t. the "
                               "domain.")
        for side_effect in number_set.membershipSideEffects(judgment):
            yield side_effect
        
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the number set under 
        the given assumptions.
        '''
        element = self.element
        
        # See if the element is known to be equal with something
        # that is known to be in the number set.
        assumptions_set = set(defaults.checkedAssumptions(assumptions))
        for eq, equiv_elem in Equals.knownRelationsFromLeft(element, 
                                                             assumptions_set):
            try:
                equiv_elem_in_set = InSet(equiv_elem, self.number_set)
                equiv_elem_in_set.prove(assumptions, automation=False)
                return eq.subLeftSideInto(equiv_elem_in_set, assumptions)
            except ProofFailure:
                pass
        
        '''
        # Maybe let's not simplify first.  If
        # See if we can simplify the element first.
        if hasattr(element, 'simplification'):
            simplification = element.simplification(assumptions=assumptions)
            element = simplification.rhs
            if element != self.element:
                # Prove membersip for the simplified element
                elem_in_set = InSet(element, self.number_set).prove(assumptions)
                # Substitute into the original.
                return simplification.subLeftSideInto(elem_in_set, assumptions)
        '''
        
        # Try the 'deduceInNumberSet' method.
        if hasattr(element, 'deduceInNumberSet'):
            return element.deduceInNumberSet(self.number_set, 
                                             assumptions=assumptions)
        else:
            msg = str(element) + " has no 'deduceInNumberSet' method."
            raise ProofFailure(InSet(self.element, self.number_set), 
                                assumptions, msg)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        return self.number_set.deduceMembershipInBool(self.element,
                                                      assumptions=assumptions)

