from proveit import Literal, BinaryOperation, USE_DEFAULTS, tryDerivation
from proveit.logic.boolean.booleans import deduceInBool, TRUE, FALSE
from proveit.logic.boolean.conjunction import compose
from implies import Implies
from proveit.common import A, B, C

IFF = Literal(__package__, stringFormat = '<=>', latexFormat = r'\Leftrightarrow')

# if and only if: A => B and B => A
class Iff(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, IFF, A, B)
        self.A = A
        self.B = B

    @classmethod
    def operatorOfOperation(subClass):
        return IFF
        
    def deriveSideEffects(self, knownTruth):
        '''
        From :math:`A \Leftrightarrow B`, automatically derive
        :math:`A \Rightarrow B`, :math:`B \Rightarrow A`, :math:`B \Leftrightarrow A`,
        and, if :math:`A \in \mathbb{B}` and :math:`B \in \mathbb{B}`, derive
        :math:`A = B` as well.
        '''
        tryDerivation(self.deriveLeftImplication, knownTruth.assumptions)
        tryDerivation(self.deriveRightImplication, knownTruth.assumptions)
        tryDerivation(self.deriveReversed, knownTruth.assumptions)
        tryDerivation(self.deriveEquality, knownTruth.assumptions)
            
    def conclude(self, assumptions):
        '''
        Attempt to conclude :math:`A \Leftrightarrow B` automatically from
        :math:`A \Rightarrow B` and :math:`B \Rightarrow A`.
        '''
        self.concludeViaComposition(assumptions)            

    def deriveLeftImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        from _theorems_ import iffImpliesLeft
        return iffImpliesLeft.specialize({A: self.A, B: self.B}, assumptions)
        
    def deriveLeft(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        return self.deriveLeftImplication(assumptions).deriveConclusion(assumptions)

    def deriveRightImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        from _theorems_ import iffImpliesRight
        return iffImpliesRight.specialize({A: self.A, B: self.B}, assumptions)

    def deriveRight(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        return self.deriveRightImplication().deriveConclusion(assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        from _theorems_ import iffSymmetry
        return iffSymmetry.specialize({A:self.A, B:self.B}, assumptions)
    
    def applyTransitivity(self, otherIff, assumptions=USE_DEFAULTS):
        '''
        From A <=> B (self) and the given B <=> C (otherIff) derive and return 
        (A <=> C) assuming self and otherIff.
        Also works more generally as long as there is a common side to the equations.
        '''
        from _theorems_ import iffTransitivity
        assert isinstance(otherIff, Iff)
        if self.B == otherIff.A:
            # from A <=> B, B <=> C, derive A <=> C
            compose(self, otherIff) # A <=> B and B <=> C
            return iffTransitivity.specialize({A:self.A, B:self.B, C:otherIff.B}).deriveConclusion(assumptions)
        elif self.A == otherIff.A:
            # from y = x and y = z, derive x = z
            return self.deriveReversed(assumptions).applyTransitivity(otherIff, assumptions)
        elif self.A == otherIff.B:
            # from y = x and z = y, derive x = z
            return self.deriveReversed(assumptions).applyTransitivity(otherIff.deriveReversed(assumptions))
        elif self.B == otherIff.B:
            # from x = y and z = y, derive x = z
            return self.applyTransitivity(otherIff.deriveReversed(assumptions))
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
        
    def definition(self):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        from _axioms_ import iffDef
        return iffDef.specialize({A:self.A, B:self.B})
    
    def concludeViaComposition(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        AimplB = Implies(self.A, self.B) 
        BimplA = Implies(self.B, self.A) 
        compose(AimplB, BimplA)
        return self.definition().deriveLeftViaEquivalence(assumptions)
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from _theorems_ import iffTT, iffTF, iffFT, iffFF # load in truth-table evaluations
        return BinaryOperation.evaluate(self, assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        from _theorems_ import iffClosure
        return iffClosure.specialize({A:self.hypothesis, B:self.conclusion}, assumptions)
    
    def deriveEquality(self, assumptions=USE_DEFAULTS):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        from _theorems_ import iffOverBoolImplEq
        return iffOverBoolImplEq.specialize({A:self.A, B:self.B}, assumptions)
