from proveit import (Literal, Operation, Conditional, 
                     defaults, USE_DEFAULTS, ProofFailure, InnerExpr)
from proveit.logic.equality import SimplificationError
from proveit._common_ import j,k,l,m, n, A, B, C, D, E, F, G
from proveit.logic.boolean.booleans import inBool
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, groupCommutation, groupCommute

class And(Operation):
    # The operator of the And operation
    _operator_ = Literal(stringFormat='and', latexFormat=r'\land', context=__file__)
    
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        Operation.__init__(self, And._operator_, operands)
    
    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce "And() = TRUE" and "And(a) = a".
        '''
        if len(self.operands) == 0:
            from proveit.logic.boolean.conjunction._theorems_ import \
                emptyConjunctionEval
            if emptyConjunctionEval.isUsable():
                return emptyConjunctionEval
        elif self.operands.is_singular():
            try:
                return self.unaryReduction(assumptions)
            except:
                # Cannot do the reduction if the operand is not known
                # to be a boolean.
                pass
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this conjunction via composing the constituents.
        That is, conclude some :math:`A \land B \and ... \land Z` via
        :math:'A', :math:'B', ..., :math:'Z' individually.
        '''
        from proveit import ExprRange
        from ._theorems_ import trueAndTrue
        if self == trueAndTrue.expr: return trueAndTrue # simple special case
        if (len(self.operands) == 1 and 
                isinstance(self.operands[0], ExprRange) and
                self.operands[0].is_parameter_independent):
            return self.concludeAsRedundant(assumptions)
        return self.concludeViaComposition(assumptions)

    def concludeNegation(self, assumptions=USE_DEFAULTS):
        # Created by JML on 6/24/19
        from ._theorems_ import (trueAndFalseNegated, falseAndTrueNegated, 
                                 falseAndFalseNegated, nandIfNeither, 
                                 nandIfLeftButNotRight, nandIfRightButNotLeft)
        from proveit.logic import Not
        not_self = Not(self)
        if not_self in {trueAndFalseNegated.expr, falseAndTrueNegated.expr, falseAndFalseNegated.expr}:
            # should be disproven via one of the imported theorems as a simple special case
            return not_self.prove()
            # Prove that the conjunction is true by proving that one of its operands is false and then negate it.
        # In the first attempt, don't use automation to prove any of the operands so that
        # we don't waste time trying to prove operands when we already know one to be false
        for useAutomationForOperand in [False, True]:
            disprovenOperandIndices = []
            for _k, operand in enumerate(self.operands):
                try:
                    operand.disprove(assumptions, automation=useAutomationForOperand)
                    disprovenOperandIndices.append(_k)
                    # possible way to prove it
                    self.concludeViaExample(operand, assumptions=assumptions)  
                except ProofFailure:
                    pass
            if len(self.operands) == 2 and len(disprovenOperandIndices) > 0:
                # One or both of the two operands were known to be true (without automation).
                # Try a possibly simpler proof than concludeViaExample.
                try:
                    if len(disprovenOperandIndices) == 2:
                        return nandIfNeither.instantiate({A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                    elif disprovenOperandIndices[0] == 0:
                        return nandIfRightButNotLeft.instantiate({A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                    else:
                        return nandIfLeftButNotRight.instantiate({A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                except:
                    pass
            if len(disprovenOperandIndices) > 0:
                # Not(self) should have been proven via 
                # concludeViaExample above 
                try:
                    return not_self.prove(assumptions, automation=False)
                except:
                    # If it wasn't proven via concludeViaExample, let's
                    # call it again to raise the appropriate exception.
                    operand = self.operands[disprovenOperandIndices[0]]
                    return self.concludeViaExample(operand, assumptions=assumptions)
        raise ProofFailure(not_self, assumptions, 
                           "Unable to conclude the negated conjunction; "
                           "we could not disprove any of the conjunction "
                           "operands.")
    
    def sideEffects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''

        from proveit.logic import Not
        if len(self.operands)==0:
            return # No side-effects needed for [And]().
        if len(self.operands) == 2:
            if self.operands[1] == Not(self.operands[0]):
                # (A or not(A)) is an unfolded Boolean
                return  # stop to avoid infinite recursion.
        yield self.deriveInBool
        yield self.deriveParts
        #yield self.deriveCommutation

    def negationSideEffects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for Not(A and B and .. and .. Z).
        '''
        from proveit.logic import Not, Or
        yield self.deriveInBool # (A and B and ... and Z) in Booleans
        # implemented by JML on 7/2/19
        # If all of the operands are negated call the disjunction form of DeMorgan's
        if all(isinstance(operand, Not) for operand in self.operands):
            demorganOr = Or(*[operand.operand for operand in self.operands])
            yield demorganOr.concludeViaDemorgans
        
    def inBoolSideEffects(self, judgment):
        '''
        From (A and B and .. and Z) in Booleans deduce (A in Booleans), (B in Booleans), ...
        (Z in Booleans).
        '''
        yield self.deducePartsInBool
    
    def deriveInBool(self, assumptions=USE_DEFAULTS):
        '''
        From (A and B and ... and Z) derive [(A and B and ... and Z) in Booleans].
        '''
        return inBool(self).prove(assumptions=assumptions)
    
    def deriveParts(self, assumptions=USE_DEFAULTS):
        r'''
        From (A and B and ... and Z)` derive each operand:
        A, B, ..., Z.
        '''
        from proveit import ExprRange
        for i, operand in enumerate(self.operands):
            if isinstance(operand, ExprRange):
                pass
            else:
                self.deriveAny(i, assumptions)            

    def deriveAny(self, index_or_expr, assumptions=USE_DEFAULTS):
        r'''
        From (A and ... and X and ... and Z) derive X.  
        indexOrExpr specifies X, either by index or the expression.
        '''
        from proveit import ExprRange
        from ._theorems_ import (anyFromAnd, leftFromAnd, rightFromAnd,
                                 from_unary_and)
        if isinstance(index_or_expr, int):
            idx = index_or_expr
        else:
            idx = list(self.operands).index(index_or_expr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        has_range_operands = any(isinstance(operand, ExprRange) 
                                 for operand in self.operands)
        if len(self.operands)==1 and not has_range_operands:
            with defaults.disabled_auto_reduction_types as disabled_types:
                disabled_types.add(And)
                return from_unary_and.instantiate({A:self.operands[0]},
                                                  assumptions=assumptions)
        if len(self.operands)==2 and not has_range_operands:
            # Two operand special case:
            if idx==0:
                return leftFromAnd.instantiate(
                        {A:self.operands[0], B:self.operands[1]}, 
                        assumptions=assumptions)
            elif idx==1:
                return rightFromAnd.instantiate(
                        {A:self.operands[0], B:self.operands[1]}, 
                        assumptions=assumptions)
        else:
            # Multiple operands.
            from proveit.core_expr_types import Len
            operand_to_extract = self.operands[idx]
            if isinstance(operand_to_extract, ExprRange):
                # Derive the conjunction of a range of operands.
                return self.deriveSomeFromAnd(idx, assumptions)
            else:
                A_sub = self.operands[:idx]
                B_sub = self.operands[idx]
                C_sub = self.operands[idx+1:]
                m_val = Len(A_sub).computed(assumptions)
                n_val = Len(C_sub).computed(assumptions)
                return anyFromAnd.instantiate(
                        {m:m_val, n:n_val, A:A_sub, B:B_sub, C:C_sub},
                        assumptions=assumptions)
    
    def deriveSome(self, start_idx, end_idx=None, assumptions=USE_DEFAULTS):
        '''
        From (A and ... and B and ... Z) derive a range of the
        conjunction, such as (C and ... and F).  Specify the range
        by providing the start and end indices (inclusive) w.r.t. 
        operand entries.  If end_idx is not provided, it defaults
        to start_idx for a single entry which should be an ExprRange.
        '''
        from proveit.core_expr_types import Len
        from proveit.logic.boolean.conjunction._theorems_ import someFromAnd
        if end_idx is None:
            end_idx = start_idx
        A_sub = self.operands[:start_idx]
        B_sub = self.operands[start_idx:end_idx+1]
        C_sub = self.operands[end_idx+1:]
        l_val = Len(A_sub).computed(assumptions)
        m_val = Len(B_sub).computed(assumptions)
        n_val = Len(C_sub).computed(assumptions)
        return someFromAnd.instantiate({l:l_val, m: m_val, n: n_val, 
                                       A:A_sub, B:B_sub, C:C_sub}, 
                                       assumptions = assumptions)

    def deriveLeft(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`A`.
        '''
        if len(self.operands) != 2:
            raise Exception('deriveLeft only applicable for binary conjunction operations')
        return self.deriveAny(0, assumptions)

    def deriveRight(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`B`.
        '''
        if len(self.operands) != 2:
            raise Exception('deriveRight only applicable for binary conjunction operations')
        return self.deriveAny(1, assumptions)
    
    def unaryReduction(self, assumptions=USE_DEFAULTS):
        from proveit.logic.boolean.conjunction._theorems_ import \
            unary_and_reduction
        if not self.operands.is_singular():
            raise ValueError("Expression must have a single operand in "
                             "order to invoke unaryReduction")
        operand = self.operands[0]
        with defaults.disabled_auto_reduction_types as disable_reduction_types:
            disable_reduction_types.add(And)
            return unary_and_reduction.instantiate({A:operand},
                                                  assumptions=assumptions)

    def concludeViaComposition(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return some (A and B ... and ... Z) via A, B, ..., Z each proven individually.
        See also the compose method to do this constructively.
        '''
        return compose(*self.operands, assumptions=assumptions)
    
    def deduceLeftInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Booleans from (A and B) in Booleans.
        '''
        from ._axioms_ import leftInBool
        if len(self.operands) == 2:
            leftInBool.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        
    def deduceRightInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce B in Booleans from (A and B) in Booleans.
        '''
        from ._axioms_ import rightInBool
        if len(self.operands) == 2:
            rightInBool.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deducePartsInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Booleans, B in Booleans, ..., Z in Booleans
        from (A and B and ... and Z) in Booleans.
        '''
        for i in range(len(self.operands)):
            self.deducePartInBool(i, assumptions)        

    def deducePartInBool(self, indexOrExpr, assumptions=USE_DEFAULTS):
        '''
        Deduce X in Booleans from (A and B and .. and X and .. and Z) in Booleans
        provided X by expression or index number.
        '''
        from ._theorems_ import eachInBool
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        if len(self.operands)==2:
            if idx == 0:
                return self.deduceLeftInBool(assumptions)
            elif idx==1:
                return self.deduceRightInBool(assumptions)
        else:
            from proveit.number import num
            mVal, nVal = num(idx), num(len(self.operands)-idx-1)
            return eachInBool.instantiate({m:mVal, n:nVal, A:self.operands[:idx], B:self.operands[idx], C:self.operands[idx+1:]}, assumptions=assumptions)

    def concludeViaDemorgans(self, assumptions=USE_DEFAULTS):
        '''
        # created by JML 6/28/19
        From A and B and C conclude Not(Not(A) or Not(B) or Not(C))
        '''
        from ._theorems_ import demorgansLawOrToAnd, demorgansLawOrToAndBin
        from proveit.number import num
        if len(self.operands) == 2:
            return demorgansLawOrToAndBin.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return demorgansLawOrToAnd.instantiate({m:num(len(self.operands)), A:self.operands}, assumptions=assumptions)

    def concludeViaExample(self, trueOperand, assumptions=USE_DEFAULTS):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the set of BOOLEANS.
        '''
        from proveit.number import num
        from ._theorems_ import nandIfNotOne, nandIfNotLeft, nandIfNotRight
        index = self.operands.index(trueOperand)
        if len(self.operands) == 2:
            if index == 0:
                return nandIfNotLeft.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
            elif index == 1:
                return nandIfNotRight.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        return nandIfNotOne.instantiate({m:num(index), n:num(len(self.operands)-index-1), A:self.operands[:index], B:self.operands[index], C:self.operands[index+1:]}, assumptions=assumptions)
    
    def concludeAsRedundant(self, assumptions=USE_DEFAULTS):
        '''
        Conclude an expression of the form
        A and ..n repeats.. and A
        given n in Naturals and A is TRUE.
        '''
        from proveit import ExprRange
        from proveit.number import one
        from ._theorems_ import redundant_conjunction
        if (len(self.operands) != 1 or 
                not isinstance(self.operands[0], ExprRange) or
                not self.operands[0].is_parameter_independent):
            raise ValueError("`And.concludeAsRedundant` only allowed for a "
                             "conjunction of the form "
                             "A and ..n repeats.. and A, not %s"%self)
        if self.operands[0].start_index != one:
            raise NotImplementedError("'concludeAsRedundant' only implemented "
                                      "when the start index is 1.  Just need to "
                                      "do an ExprRange shift to implement it more "
                                      "completely")
        _A = self.operands[0].body
        return redundant_conjunction.instantiate(
                {n:self.operands[0].end_index, A:_A}, assumptions=assumptions)

    def evaluation(self, assumptions=USE_DEFAULTS, *, automation=True,
                   minimal_automation=False, **kwargs):
        '''
        Attempt to determine whether this conjunction evaluates
        to true or false under the given assumptions.  If automation
        is False, it will only succeed if the evaluation is already
        known.  If automation and minimal_automation are True, it will 
        only rely upon known  evaluations of the operands to determine 
        whether to try to prove or disprove the conjunction.
        '''
        from proveit.logic import FALSE
        from ._axioms_ import andTT, andTF, andFT, andFF # load in truth-table evaluations
        if len(self.operands)==0:
            return self.unaryReduction(assumptions)
        
        # First just see if it has a known evaluation.
        try:
            return Operation.evaluation(self, assumptions, automation=False)
        except SimplificationError as e:
            if not automation: 
                raise e
    
        # Depending upon evaluations of operands, we will either
        # attempt to prove or disprove this conjunction.
        if minimal_automation:
            # Only do non-automated evaluations of operands
            # if minimal_automation is True.
            operand_automations = (False,)
        else:
            # First try non-automated operand evaluation, then
            # automated only if necessary.
            operand_automations = (False, True)
        for operand_automation in operand_automations:
            operands_evals = []
            for operand in self.operands:
                try:
                    operand_eval = operand.evaluation(
                            assumptions, automation=operand_automations)
                    operands_evals.append(operand_eval.rhs)
                except:
                    operands_evals.append(None)
            if FALSE in operands_evals:
                # If any operand is untrue, the conjunction may
                # only evaluate to false if it can be evaluated.
                self.disprove(assumptions)
                break
            elif not None in operands_evals:
                # If no operand is untrue and all the evaluations
                # are known, the conjunction may only evaluate
                # to true if it can be evaluated.
                self.prove(assumptions)
                break
        
        # If we had any success proving or disproving this conjunction
        # there should be a known evaluation now.
        return Operation.evaluation(self, assumptions, automation=False)
    
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        
        from ._theorems_ import binaryClosure, closure
        if len(self.operands)==2:
            return binaryClosure.instantiate({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            from proveit.number import num    
        return closure.instantiate({m:num(len(self.operands)), A:self.operands}, assumptions=assumptions)

    def commutation(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index initIdx has been moved to finalIdx.
        For example, (A and B and ... and Y and Z) = (A and ... and Y and B and Z)
        via initIdx = 1 and finalIdx = -2.
        '''
        from ._theorems_ import commutation, leftwardCommutation, rightwardCommutation
        return apply_commutation_thm(self, initIdx, finalIdx, commutation, leftwardCommutation, rightwardCommutation, assumptions)

    def groupCommutation(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operands
        at indices [initIdx, initIdx+length) have been moved to [finalIdx. finalIdx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return groupCommutation(self, initIdx, finalIdx, length, disassociate, assumptions)
    
    def commute(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which the operand
        at index initIdx has been moved to finalIdx.
        For example, given (A and B and ... and Y and Z) derive (A and ... and Y and B and Z)
        via initIdx = 1 and finalIdx = -2.
        '''
        from ._theorems_ import commute, leftwardCommute, rightwardCommute      
        return apply_commutation_thm(self, initIdx, finalIdx, commute, leftwardCommute, rightwardCommute, assumptions)  
    
    def groupCommute(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        '''
        Given self, deduce and return a form in which the operands
        at indices [initIdx, initIdx+length) have been moved to [finalIdx. finalIdx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return groupCommute(self, initIdx, finalIdx, length, disassociate, assumptions)
    
    def association(self, startIdx, length, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which operands in the
        range [startIdx, startIdx+length) are grouped together.
        For example, (A and B and ... and Y and Z) = (A and B ... and (L and ... and M) and ... and Y and Z)
        '''
        from ._theorems_ import association
        return apply_association_thm(self, startIdx, length, association, assumptions)

    def associate(self, startIdx, length, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which operands in the
        range [startIdx, startIdx+length) are grouped together.
        For example, from (A and B and ... and Y and Z) derive
        (A and B ... and (L and ... and M) and ... and Y and Z).
        '''
        from ._theorems_ import associate
        return apply_association_thm(self, startIdx, length, associate, assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (A and B ... and (L and ... and M) and ... and Y and Z) = (A and B and ... and Y and Z)
        '''
        from ._theorems_ import disassociation
        return apply_disassociation_thm(self, idx, disassociation, assumptions)

    def disassociate(self, idx, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which the operand
        at the given index is ungrouped.
        For example, from (A and B ... and (L and ... and M) and ... and Y and Z)
        derive (A and B and ... and Y and Z).
        '''
        from ._theorems_ import disassociate
        return apply_disassociation_thm(self, idx, disassociate, assumptions)

    
def compose(*expressions, assumptions=USE_DEFAULTS):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    if len(expressions)==0:
        from proveit.logic.boolean.conjunction._axioms_ import \
            emptyConjunction
        return emptyConjunction
    if len(expressions)==2:
        from ._theorems_ import andIfBoth
        return andIfBoth.instantiate({A:expressions[0], B:expressions[1]}, assumptions=assumptions)
    else:
        from proveit.number import num
        from ._theorems_ import andIfAll
        return andIfAll.instantiate({m:num(len(expressions)), A:expressions}, assumptions=assumptions)

# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(And, 'commutation', 'commuted', 'commute')
InnerExpr.register_equivalence_method(And, 'groupCommutation', 'groupCommuted', 'groupCommute')
InnerExpr.register_equivalence_method(And, 'association', 'associated', 'associate')
InnerExpr.register_equivalence_method(And, 'disassociation', 'disassociated', 'disassociate')
