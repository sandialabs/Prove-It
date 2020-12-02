from proveit import Literal, Operation, USE_DEFAULTS
from proveit.logic.boolean.conjunction import compose
from .implies import Implies
from proveit._common_ import A, B, C
from proveit import TransitiveRelation

# if and only if: A => B and B => A
class Iff(TransitiveRelation):
    # The operator of the Iff operation
    _operator_ = Literal(stringFormat='<=>', latexFormat=r'\Leftrightarrow', theory=__file__)

    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()        
        
    def __init__(self, A, B):
        TransitiveRelation.__init__(self, Iff._operator_, A, B)
        self.A = A
        self.B = B

    
    def sideEffects(self, judgment):
        '''
        Yield the TransitiveRelation side-effects (which also records knownLeftSides
        and knownRightSides).  Also derive the left and right implications,
        derive the reversed version and attempt to derive equality.
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, judgment):
            yield sideEffect
        yield self.deriveLeftImplication # B=>A given A<=>B
        yield self.deriveRightImplication # A=>B given A<=>B
        yield self.deriveReversed # B<=>A given A<=>B
        yield self.deriveEquality # A=B given A<=>B (assuming A and B are in booleans)
            
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this bi-directional implication by 
        reducing its operands to true/false.
        '''
        from ._theorems_ import  iffTT, iffTF, iffFT, iffFF, trueIffTrue, falseIffFalse
        if self in {trueIffTrue, falseIffFalse}:
            # should be proven via one of the imported theorems as a simple special case
            try:
                self.evaluation(assumptions)
            except:
                return self.prove()
        try:
            # try to prove the bi-directional implication via evaluation reduction.
            # if that is possible, it is a relatively straightforward thing to do.
            return Operation.conclude(assumptions)
        except:
            pass
        try:
            # Use a breadth-first search approach to find the shortest
            # path to get from one end-point to the other.
            return TransitiveRelation.conclude(self, assumptions)            
        except:
            pass            
            
        # the last attempt is to introduce the Iff via implications each way, an
        # essentially direct consequence of the definition.
        return self.concludeByDefinition(assumptions)

    def concludeNegation(self, assumptions=USE_DEFAULTS):
        # implemented by Joaquin on 6/17/19
        from proveit.logic.boolean._common_ import FALSE, TRUE
        try:
            if self.A == TRUE and self.B == FALSE:
                from ._theorems_ import trueIffFalseNegated, falseIffTrueNegated
            elif self.B == TRUE and self.A == FALSE:
                from ._theorems_ import trueIffFalseNegated, falseIffTrueNegated
        except:
            pass

    def deriveLeftImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        from ._theorems_ import iffImpliesLeft
        return iffImpliesLeft.instantiate({A: self.A, B: self.B}, assumptions=assumptions)
        
    def deriveLeft(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        from ._theorems_ import leftFromIff
        return leftFromIff.instantiate({A:self.A, B:self.B}, assumptions=assumptions)

    def deriveRightImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        from ._theorems_ import iffImpliesRight
        return iffImpliesRight.instantiate({A: self.A, B: self.B}, assumptions=assumptions)

    def deriveRight(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        from ._theorems_ import rightFromIff
        return rightFromIff.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        from ._theorems_ import iffSymmetry
        return iffSymmetry.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
    
    def applyTransitivity(self, otherIff, assumptions=USE_DEFAULTS):
        '''
        From A <=> B (self) and the given B <=> C (otherIff) derive and return 
        (A <=> C) assuming self and otherIff.
        Also works more generally as long as there is a common side to the equations.
        '''
        from ._theorems_ import iffTransitivity
        assert isinstance(otherIff, Iff)
        if self.B == otherIff.A:
            # from A <=> B, B <=> C, derive A <=> C
            return iffTransitivity.instantiate({A:self.A, B:self.B, C:otherIff.B}, assumptions=assumptions)
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
        from ._axioms_ import iffDef
        return iffDef.instantiate({A:self.A, B:self.B})
    
    def concludeByDefinition(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        from ._theorems_ import iffIntro
        return iffIntro.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
    
    def evaluation(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from ._theorems_ import iffTT, iffTF, iffFT, iffFF # IMPORTANT: load in truth-table evaluations
        return Operation.evaluation(self, assumptions, automation)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        from ._theorems_ import iffClosure
        return iffClosure.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
    
    def deriveEquality(self, assumptions=USE_DEFAULTS):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        from ._theorems_ import eqFromIff, eqFromMutualImpl
        # We must be able to prove this Iff to do this derivation --
        # then either eqFromIff or eqFromMutualImpl can be used.
        self.prove(assumptions=assumptions) 
        # eqFromMutualImpl may make for a shorter proof; do it both ways (if both are usable)
        if not eqFromIff.isUsable():
            return eqFromMutualImpl.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
        eqFromMutualImpl.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
        return eqFromIff.instantiate({A:self.A, B:self.B}, assumptions=assumptions)
