from proveit import Expression, Literal, Operation, ExprList
from proveit import OperationOverInstances #AssociativeOperation,
from proveit._common_ import a, b, n
from proveit.logic import Forall, Implies, InSet, Or, NotEquals #generateSubExpressions
from proveit.number import Reals, Complexes, Naturals, Integers, NaturalsPos, RealsPos, RealsNeg
pkg = __package__

class NumberOp:
    def __init__(self):
        pass

    def _closureTheorem(self, numberSet):
        pass # may be implemented by derived class

    def _notEqZeroTheorem(self):
        pass # may be implemented by derived class
    
    def _positiveTheorem(self):
        pass # may be implemented by derived class
    
    def _negativeTheorem(self):
        pass # may be implemented by derived class
    
    def deduceInIntegers(self, assumptions=frozenset()):
        return deduceInNumberSet(self, Integers, assumptions)

    def deduceInNaturals(self, assumptions=frozenset()):
        return deduceInNumberSet(self, Naturals, assumptions)
        
    def deduceInNaturalsPos(self, assumptions=frozenset()):
        return deduceInNumberSet(self, NaturalsPos, assumptions)
    
    def deduceInReals(self, assumptions=frozenset()):
        return deduceInNumberSet(self, Reals, assumptions)

    def deduceInRealsPos(self, assumptions=frozenset()):
        return deduceInNumberSet(self, RealsPos, assumptions)

    def deduceInRealsNeg(self, assumptions=frozenset()):
        return deduceInNumberSet(self, RealsNeg, assumptions)

    def deduceInComplexes(self, assumptions=frozenset()):
        return deduceInNumberSet(self, Complexes, assumptions)

    def deduceInIntegersDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, Integers, assumptions) 

    def deduceInNaturalsDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, Naturals, assumptions) 
        
    def deduceInNaturalsPosDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, NaturalsPos, assumptions) 
    
    def deduceInRealsDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, Reals, assumptions) 

    def deduceInRealsPosDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, RealsPos, assumptions) 

    def deduceInRealsNegDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, RealsNeg, assumptions) 

    def deduceInComplexesDirectly(self, assumptions=frozenset()):
        # override as an alternate to supplying a _closureTheorem
        raise DeduceInNumberSetException(self, Complexes, assumptions) 

    def deduceNotZero(self, assumptions=frozenset()):
        return deduceNotZero(self, assumptions)

    def deducePositive(self, assumptions=frozenset()):
        return deducePositive(self, assumptions)

    def deduceNegative(self, assumptions=frozenset()):
        return deduceNegative(self, assumptions)
    
def deduceInNumberSet(exprOrList, numberSet, assumptions=frozenset(), ruledOutSets=frozenset(), dontTryPos=False, dontTryNeg=False):
    '''
    For each given expression, attempt to derive that it is in the specified numberSet
    under the given assumptions.  If ruledOutSets is provided, don't attempt to
    derive it from being in a subset in ruledOutSets.
    If successful, returns the deduced statement, otherwise raises an Exception.   
    '''
    from proveit.number._common_ import ComplexesSansZero

    if not isinstance(assumptions, set) and not isinstance(assumptions, frozenset):
        raise Exception('assumptions should be a set')

    if not isinstance(exprOrList, Expression) or isinstance(exprOrList, ExprList):
        # If it isn't an Expression, assume it's iterable and deduce each
        return [deduceInNumberSet(expr, numberSet=numberSet, assumptions=assumptions) for expr in exprOrList]    
    expr = exprOrList # just a single expression

    try:
        return InSet(expr, numberSet).prove(assumptions)
    except:
        pass # not so simple, keep trying (below)
        
    if NaturalsPos not in ruledOutSets and (numberSet == Naturals or numberSet == Complexes or 
                                            numberSet == RealsPos or numberSet == Reals or 
                                            numberSet == Integers):
        try:
            # try deducing in the NaturalsPos as a subset of the desired numberSet
            deduceInNumberSet(expr, NaturalsPos, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                natural.theorems.inNatPos_inComplexes.specialize({a:expr})
            elif numberSet == RealsPos:
                natural.theorems.inNatPos_inRealsPos.specialize({a:expr})
            elif numberSet == Reals:
                natural.theorems.inNatPos_inReals.specialize({a:expr})
            elif numberSet == Integers:
                natural.theorems.inNatPos_inIntegers.specialize({a:expr})
            elif numberSet == Naturals:
                natural.theorems.inNatPos_inNaturals.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {NaturalsPos} # ruled out Naturals
    if Naturals not in ruledOutSets and (numberSet == Complexes or 
                                         numberSet == Reals or numberSet == Integers):
        try:
            # try deducing in the Naturals as a subset of the desired numberSet
            deduceInNumberSet(expr, Naturals, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                natural.theorems.inComplexes.specialize({a:expr})
            elif numberSet == Reals:
                natural.theorems.inReals.specialize({a:expr})
            elif numberSet == Integers:
                natural.theorems.inIntegers.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {Naturals} # ruled out Naturals
    if Integers not in ruledOutSets and (numberSet == Complexes or numberSet == Reals):
        try:
            # try deducing in the Integers as a subset of the desired numberSet
            deduceInNumberSet(expr, Integers, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                integer.theorems.inComplexes.specialize({a:expr})
            elif numberSet == Reals:
                integer.theorems.inReals.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {Integers} # ruled out Integers
    if not dontTryPos and numberSet == RealsPos:
        try:
            # try deducing in the RealsPos for greater than zero
            deducePositive(expr, assumptions=assumptions, dontTryRealsPos=True)
            deduceInReals(expr, assumptions)
            return real.theorems.inRealsPos_iff_positive.specialize({a:expr}).deriveLeft()
        except:
            pass
    if not dontTryNeg and numberSet == RealsNeg:
        try:
            # try deducing in the RealsNeg for greater than zero
            deduceNegative(expr, assumptions=assumptions, dontTryRealsNeg=True)
            deduceInReals(expr, assumptions)
            return real.theorems.inRealsNeg_iff_negative.specialize({a:expr}).deriveLeft()
        except:
            pass
    if RealsPos not in ruledOutSets and (numberSet == Complexes or numberSet == Reals):
        try:
            # try deducing in the RealsPos as a subset of the desired numberSet
            deduceInNumberSet(expr, RealsPos, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                real.theorems.inRealsPos_inComplexes.specialize({a:expr})
            elif numberSet == Reals:
                real.theorems.inRealsPos_inReals.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {RealsPos} # ruled out Reals
    if RealsNeg not in ruledOutSets and (numberSet == Complexes or numberSet == Reals):
        try:
            # try deducing in the RealsNeg as a subset of the desired numberSet
            deduceInNumberSet(expr, RealsNeg, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                real.theorems.inRealsNeg_inComplexes.specialize({a:expr})
            elif numberSet == Reals:
                real.theorems.inRealsNeg_inReals.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {RealsNeg} # ruled out Reals
    if Reals not in ruledOutSets and numberSet == Complexes:
        try:
            # try deducing in the Reals as a subset of the desired numberSet
            deduceInNumberSet(expr, Reals, assumptions=assumptions, ruledOutSets=ruledOutSets)
            if numberSet == Complexes:
                real.theorems.inComplexes.specialize({a:expr})
            return In(expr, numberSet).checked(assumptions)
        except:
            ruledOutSets = ruledOutSets | {Reals} # ruled out Reals

    # Couldn't deduce in a subset.  Try using a closure theorem.
    if numberSet == ComplexesSansZero:
        # special case for numberSet = Complexes - {0}
        closureThm = complex.theorems.inComplexesSansZero
        closureSpec = closureThm.specialize({a:expr})        
    else:
        if not isinstance(expr, NumberOp):
            # See of the Expression class has deduceIn[numberSet] method (as a last resort):
            if numberSet == Naturals and hasattr(expr, 'deduceInNaturals'):
                return expr.deduceInNaturals()
            elif numberSet == NaturalsPos and hasattr(expr, 'deduceInNaturalsPos'):
                return expr.deduceInNaturalsPos()
            elif numberSet == Integers and hasattr(expr, 'deduceInIntegers'):
                return expr.deduceInIntegers()
            elif numberSet == Reals and hasattr(expr, 'deduceInReals'):
                return expr.deduceInReals()
            elif numberSet == RealsPos and hasattr(expr, 'deduceInRealsPos'):
                return expr.deduceInRealsPos()
            elif numberSet == RealsNeg and hasattr(expr, 'deduceInRealsNeg'):
                return expr.deduceInRealsNeg()
            elif numberSet == Complexes and hasattr(expr, 'deduceInComplexes'):
                return expr.deduceInComplexes()          
            # Ran out of options:  
            raise DeduceInNumberSetException(expr, numberSet, assumptions)
        closureThm = expr._closureTheorem(numberSet)
        if closureThm is None:
            if numberSet == Naturals and hasattr(expr, 'deduceInNaturalsDirectly'):
                return expr.deduceInNaturalsDirectly(assumptions)
            elif numberSet == NaturalsPos and hasattr(expr, 'deduceInNaturalsPosDirectly'):
                return expr.deduceInNaturalsPosDirectly(assumptions)
            elif numberSet == Integers and hasattr(expr, 'deduceInIntegersDirectly'):
                return expr.deduceInIntegersDirectly(assumptions)
            elif numberSet == Reals and hasattr(expr, 'deduceInRealsDirectly'):
                return expr.deduceInRealsDirectly(assumptions)
            elif numberSet == RealsPos and hasattr(expr, 'deduceInRealsPosDirectly'):
                return expr.deduceInRealsPosDirectly(assumptions)
            elif numberSet == RealsNeg and hasattr(expr, 'deduceInRealsNegDirectly'):
                return expr.deduceInRealsNegDirectly(assumptions)
            elif numberSet == Complexes and hasattr(expr, 'deduceInComplexesDirectly'):
                return expr.deduceInComplexesDirectly(assumptions)
            raise DeduceInNumberSetException(expr, numberSet, assumptions)    
        # Apply the closure theorem
        assert isinstance(closureThm, Forall), 'Expecting closure theorem to be a Forall expression'
        iVars = closureThm.instanceVar
        # Specialize the closure theorem differently for AccociativeOperation and OperationOverInstances compared with other cases
        if isinstance(expr, AssociativeOperation):
            assert len(iVars) == 1, 'Expecting one instance variable for the closure theorem of an AssociativeOperation'
            assert isinstance(iVars[0], Etcetera), 'Expecting the instance variables for the closure theorem of an AssociativeOperation to be an Etcetera Variable'
            closureSpec = closureThm.specialize({iVars[0]:expr.operands})
        elif isinstance(expr, OperationOverInstances):
            # first deduce that all of the instances are in the domain
            
            # See if we can deduce that the instanceVar under the domain are in one of the number sets
            # For instance expression assumptions, remove any assumptions involving the instance variable and add assumptions 
            # that the instance variable is in the domain and add the condition assumption.
            instanceExpr_assumptions = {assumption for assumption in assumptions if assumption.freeVars().isdisjoint(expr.instanceVar)}
            instanceExpr_assumptions |= {In(instanceVar, expr.domain) for instanceVar in expr.instanceVar}
            instanceExpr_assumptions |= {condition for condition in expr.conditions}
            if hasattr(expr.domain, 'deduceMemberInNaturals'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInNaturals(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInNaturalsPos'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInNaturalsPos(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInIntegers'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInIntegers(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInReals'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInReals(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInRealsPos'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInRealsPos(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInRealsNeg'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInRealsNeg(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            elif hasattr(expr.domain, 'deduceMemberInComplexes'):
                for instanceVar in expr.instanceVar:
                    try:
                        expr.domain.deduceMemberInIntegers(instanceVar, assumptions=instanceExpr_assumptions)
                    except:
                        pass
            
            # Now we need to deduce that the instance expressions are all in the number set
            instanceExprInNumberSet = deduceInNumberSet(expr.instanceExpr, numberSet, assumptions=instanceExpr_assumptions).checked(instanceExpr_assumptions)
            instanceExprInNumberSet.generalize(expr.instanceVar, domain=expr.domain).checked(assumptions)
            
            assert len(iVars) == 2 # instance function and domain -- conditions not implemented at this time
            Pop, Pop_sub = Operation(iVars[0], expr.instanceVar), expr.instanceExpr

            innerIvars = set().union(subExpr.instanceVar[0] for subExpr in generateSubExpressions(closureThm.instanceExpr, subExprClass=OperationOverInstances))
            subMap = {Pop:Pop_sub, iVars[1]:expr.domain}
            subMap.update({innerIvar:expr.instanceVar for innerIvar in innerIvars})
            preClosureSpec = closureThm.specialize(subMap).checked()
            assert isinstance(preClosureSpec, Implies), "Expecting the OperationOverInstances closure theorem to specialize to an implication with the hypothesis being the closure forall instances"
            closureSpec = preClosureSpec.deriveConclusion()
        else:
            assert len(iVars) == len(expr.operands), 'Expecting the number of instance variables for the closure theorem to be the same as the number of operands of the Expression'
            closureSpec = closureThm.specialize({iVar:operand for iVar, operand in zip(iVars, expr.operands)})
    # deduce any of the requirements for the closureThm application

    _deduceRequirements(closureThm, closureSpec, assumptions)
    try:
        return In(expr, numberSet).checked(assumptions)
    except:
        raise DeduceInNumberSetException(expr, numberSet, assumptions)

def deduceInNaturals(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of integers.
    Warnings/errors may be suppressed by setting suppressWarnings to True.
    '''
    return deduceInNumberSet(exprOrList, Naturals, assumptions=assumptions)

def deduceInNaturalsPos(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of integers.
    Warnings/errors may be suppressed by setting suppressWarnings to True.
    '''
    return deduceInNumberSet(exprOrList, NaturalsPos, assumptions=assumptions)

def deduceInIntegers(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of integers
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.
    '''
    return deduceInNumberSet(exprOrList, Integers, assumptions=assumptions)

def deduceInReals(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of reals
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.    
    '''
    return deduceInNumberSet(exprOrList, Reals, assumptions=assumptions)

def deduceInRealsPos(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of RealsPos
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.    
    '''
    return deduceInNumberSet(exprOrList, RealsPos, assumptions=assumptions)

def deduceInRealsNeg(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of RealsNeg
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.    
    '''
    return deduceInNumberSet(exprOrList, RealsNeg, assumptions=assumptions)

def deduceInComplexes(exprOrList, assumptions=frozenset()):
    '''
    For each given expression, attempt to derive that it is in the set of complexes
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.  
    '''
    return deduceInNumberSet(exprOrList, Complexes, assumptions=assumptions)

def deduceNotZero(exprOrList, assumptions=frozenset(), dontTryPos=False, dontTryNeg=False):
    '''
    For each given expression, attempt to derive that it is not equal to zero
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.  
    '''
    from proveit.number import num
    import real.theorems
    if not isinstance(assumptions, set) and not isinstance(assumptions, frozenset):
        raise Exception('assumptions should be a set')
    if not isinstance(exprOrList, Expression) or isinstance(exprOrList, ExpressionList):
        # If it isn't an Expression, assume it's iterable and deduce each
        return [deduceNotZero(expr, assumptions=assumptions) for expr in exprOrList]
    # A single Expression:
    expr = exprOrList
    try:
        # may be done before we started
        return NotEquals(expr, num(0)).checked(assumptions)
    except:
        pass # not so simple

    if not dontTryPos:
        try:
            # see if we can deduce in positive first
            deducePositive(expr, assumptions)
            isPos = True
        except:
            isPos = False # not so simple
        if isPos:
            deduceInReals(expr, assumptions)
            return real.theorems.positive_implies_notzero.specialize({a:expr}).checked(assumptions)

    if not dontTryNeg:
        try:
            # see if we can deduce in negative first
            deduceNegative(expr, assumptions)
            isNeg = True
        except:
            isNeg = False # not so simple
        if isNeg:
            deduceInReals(expr, assumptions)
            return real.theorems.negative_implies_notzero.specialize({a:expr}).checked(assumptions)

    # Try using notEqZeroTheorem
    if not isinstance(expr, NumberOp):
        # See of the Expression class has deduceNotZero method (as a last resort):
        if hasattr(expr, 'deduceNotZero'):
            return expr.deduceNotZero()
        raise DeduceNotZeroException(expr, assumptions)
    notEqZeroThm = expr._notEqZeroTheorem()
    if notEqZeroThm is None:
        raise DeduceNotZeroException(expr, assumptions)
    assert isinstance(notEqZeroThm, Forall), 'Expecting notEqZero theorem to be a Forall expression'
    iVars = notEqZeroThm.instanceVar
    # Specialize the closure theorem differently for AccociativeOperation compared with other cases
    if isinstance(expr, AssociativeOperation):
        assert len(iVars) == 1, 'Expecting one instance variables for the notEqZero theorem of an AssociativeOperation'
        assert isinstance(iVars[0], Etcetera), 'Expecting the instance variable for the notEqZero theorem of an AssociativeOperation to be an Etcetera Variable'
        notEqZeroSpec = notEqZeroThm.specialize({iVars[0]:expr.operands})
    else:
        if len(iVars) != len(expr.operands):
            raise Exception('Expecting the number of instance variables for the closure theorem to be the same as the number of operands of the Expression')
        notEqZeroSpec = notEqZeroThm.specialize({iVar:operand for iVar, operand in zip(iVars, expr.operands)})
    # deduce any of the requirements for the notEqZeroThm application
    _deduceRequirements(notEqZeroThm, notEqZeroSpec, assumptions)
    try:
        return NotEquals(expr, num(0)).checked(assumptions)
    except:
        raise DeduceNotZeroException(expr, assumptions)

def deducePositive(exprOrList, assumptions=frozenset(), dontTryRealsPos=False):
    '''
    For each given expression, attempt to derive that it is positive
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.  
    '''
    from proveit.number import Greater, num

    if not isinstance(assumptions, set) and not isinstance(assumptions, frozenset):
        raise Exception('assumptions should be a set')

    if not isinstance(exprOrList, Expression) or isinstance(exprOrList, ExprList):
        # If it isn't an Expression, assume it's iterable and deduce each
        return [deducePositive(expr, assumptions=assumptions) for expr in exprOrList]
    # A single Expression:
    expr = exprOrList
    try:
        # may be done before we started
        return Greater(expr, num(0)).checked(assumptions)
    except:
        pass # not so simple

    if not dontTryRealsPos:
        try:
            # see if we can deduce in RealsPos first
            deduceInNumberSet(expr, RealsPos, assumptions, dontTryPos=True)
            inRealsPos = True
        except:
            inRealsPos = False # not so simple
        if inRealsPos:
            deduceInReals(expr, assumptions)
            return real.theorems.inRealsPos_iff_positive.specialize({a:expr}).deriveRight().checked(assumptions)

    # Try using positiveTheorem
    if not isinstance(expr, NumberOp):
        # See of the Expression class has deduceNotZero method (as a last resort):
        if hasattr(expr, 'deducePositive'):
            return expr.deducePositive()
        raise DeducePositiveException(expr, assumptions)
    positiveThm = expr._positiveTheorem()
    if positiveThm is None:
        raise DeducePositiveException(expr, assumptions)
    assert isinstance(positiveThm, Forall), 'Expecting deduce positive theorem to be a Forall expression'
    iVars = positiveThm.instanceVar
    # Specialize the closure theorem differently for AccociativeOperation compared with other cases
    if isinstance(expr, AssociativeOperation):
        assert len(iVars) == 1, 'Expecting one instance variables for the positive theorem of an AssociativeOperation'
        assert isinstance(iVars[0], Etcetera), 'Expecting the instance variable for the positive theorem of an AssociativeOperation to be an Etcetera Variable'
        positiveSpec = positiveThm.specialize({iVars[0]:expr.operands})
    else:
        if len(iVars) != len(expr.operands):
            raise Exception('Expecting the number of instance variables for the closure theorem to be the same as the number of operands of the Expression')
        positiveSpec = positiveThm.specialize({iVar:operand for iVar, operand in zip(iVars, expr.operands)})
    # deduce any of the requirements for the notEqZeroThm application
    _deduceRequirements(positiveThm, positiveSpec, assumptions)
    try:
        return GreaterThan(expr, num(0)).checked(assumptions)
    except:
        raise DeducePositiveException(expr, assumptions)

def deduceNegative(exprOrList, assumptions=frozenset(), dontTryRealsNeg=False):
    '''
    For each given expression, attempt to derive that it is negative
    under the given assumptions.  If successful, returns the deduced statement,
    otherwise raises an Exception.  
    '''
    from proveit.number import LessThan, num
    import real.theorems
    if not isinstance(assumptions, set) and not isinstance(assumptions, frozenset):
        raise Exception('assumptions should be a set')
    if not isinstance(exprOrList, Expression) or isinstance(exprOrList, ExpressionList):
        # If it isn't an Expression, assume it's iterable and deduce each
        return [deduceNegative(expr, assumptions=assumptions) for expr in exprOrList]
    # A single Expression:
    expr = exprOrList
    try:
        # may be done before we started
        return LessThan(expr, num(0)).checked(assumptions)
    except:
        pass # not so simple

    if not dontTryRealsNeg:
        try:
            # see if we can deduce in RealsNeg first
            deduceInNumberSet(expr, RealsNeg, assumptions, dontTryNeg=True)
            inRealsNeg = True
        except:
            inRealsNeg = False # not so simple
        if inRealsNeg:
            deduceInReals(expr, assumptions)
            return real.theorems.inRealsNeg_iff_negative.specialize({a:expr}).deriveRight().checked(assumptions)

    # Try using negativeTheorem
    if not isinstance(expr, NumberOp):
        # See of the Expression class has deduceNotZero method (as a last resort):
        if hasattr(expr, 'deduceNegative'):
            return expr.deduceNegative()
        raise DeduceNegativeException(expr, assumptions)
    negativeThm = expr._negativeTheorem()
    if negativeThm is None:
        raise DeduceNegativeException(expr, assumptions)
    assert isinstance(negativeThm, Forall), 'Expecting deduce negative theorem to be a Forall expression'
    iVars = negativeThm.instanceVar
    # Specialize the closure theorem differently for AccociativeOperation compared with other cases
    if isinstance(expr, AssociativeOperation):
        assert len(iVars) == 1, 'Expecting one instance variables for the negative theorem of an AssociativeOperation'
        assert isinstance(iVars[0], Etcetera), 'Expecting the instance variable for the negative theorem of an AssociativeOperation to be an Etcetera Variable'
        negativeSpec = negativeThm.specialize({iVars[0]:expr.operands})
    else:
        if len(iVars) != len(expr.operands):
            raise Exception('Expecting the number of instance variables for the closure theorem to be the same as the number of operands of the Expression')
        negativeSpec = negativeThm.specialize({iVar:operand for iVar, operand in zip(iVars, expr.operands)})
    # deduce any of the requirements for the notEqZeroThm application
    _deduceRequirements(negativeThm, negativeSpec, assumptions)
    try:
        return LessThan(expr, num(0)).checked(assumptions)
    except:
        raise DeduceNegativeException(expr, assumptions)

def _deduceRequirements(theorem, specializedExpr, assumptions):
    # Grab the conditions for the specialized expression of the given theorem
    # and see if we need a further deductions for those requirements.
    for stmt, _, _, conditions in specializedExpr.statement._specializers:
        if stmt._expression == theorem:
            # check each condition and apply recursively if it is in some set                
            for condition in conditions:
                condition = condition._expression
                if isinstance(condition, Or):
                    # just one of an or'd list must be satisfied
                    trueConditionOperand = None
                    for possibility in condition.operands:
                        # We need to deduce that each operand is in BOOLEANS
                        if possibility.hasattr('deduceInBools'):
                            possibility.deduceInBools(assumptions)
                        try:
                            # see if this is a satisfied condition
                            _deduceRequirement(possibility, assumptions)
                            trueConditionOperand = possibility
                        except:
                            pass
                    if trueConditionOperand is not None:
                        # conclude the "or" condition from one true condition operand
                        condition.concludeViaExample(trueConditionOperand)
                else:
                    _deduceRequirement(condition, assumptions)

def _deduceRequirement(condition, assumptions):
    from proveit.number import num, LessThan, GreaterThan, GreaterThanEquals, Abs
    from proveit.number.complex.theorems import absIsNonNeg
    if isinstance(condition, In):
        domain = condition.domain
        elem = condition.element
        deduceInNumberSet(elem, numberSet=domain, assumptions=assumptions)
    elif isinstance(condition, NotEquals) and condition.rhs == num(0):
        deduceNotZero(condition.lhs, assumptions=assumptions)
    elif isinstance(condition, GreaterThan) and condition.rhs == num(0):
        deducePositive(condition.lhs, assumptions=assumptions)
    elif isinstance(condition, GreaterThanEquals) and condition.rhs == num(0):
        if isinstance(condition.lhs, Abs):
            condition.lhs.deduceGreaterThanEqualsZero(assumptions=assumptions)
        else:
            try:
                # if it is in Naturals, this comes naturally
                deduceInNaturals(condition.lhs, assumptions)
                Naturals.deduceMemberLowerBound(condition.lhs).checked(assumptions)
            except:
                # May also extend with deduceNonNegative, but that isn't implemented yet.
                pass
    elif isinstance(condition, GreaterThanEquals) and condition.rhs == num(1):
        try:
            # if it is in NaturalsPos, this comes naturally
            deduceInNaturalsPos(condition.lhs, assumptions)
            NaturalsPos.deduceMemberLowerBound(condition.lhs).checked(assumptions)
        except:
            pass        
    elif isinstance(condition, LessThan) and condition.rhs == num(0):
        deduceNegative(condition.lhs, assumptions=assumptions)
    

class DeduceInNumberSetException(Exception):
    def __init__(self, expr, numberSet, assumptions):
        self.expr = expr
        self.numberSet = numberSet
        self.assumptions = assumptions
    def __str__(self):
        return 'Unable to prove ' + str(self.expr) + ' in ' + str(self.numberSet) + ' under assumptions: ' + str(self.assumptions)

class DeduceNotZeroException(Exception):
    def __init__(self, expr, assumptions):
        self.expr = expr
        self.assumptions = assumptions
    def __str__(self):
        return 'Unable to prove ' + str(self.expr) + ' not equal to zero under assumptions: ' + str(self.assumptions)
    
class DeducePositiveException(Exception):
    def __init__(self, expr, assumptions):
        self.expr = expr
        self.assumptions = assumptions
    def __str__(self):
        return 'Unable to prove ' + str(self.expr) + ' is positive under assumptions: ' + str(self.assumptions)

class DeduceNegativeException(Exception):
    def __init__(self, expr, assumptions):
        self.expr = expr
        self.assumptions = assumptions
    def __str__(self):
        return 'Unable to prove ' + str(self.expr) + ' is negative under assumptions: ' + str(self.assumptions)
