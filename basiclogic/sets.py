import sys
from statement import *
from context import *
from genericOperations import *
from variables import *

# set theory related literals
literals = Literals()
IN = literals.add('IN')
NOTIN = literals.add('NOTIN')
SINGLETON = literals.add('SINGLETON')
COMPLEMENT = literals.add('COMPLEMENT')
UNION = literals.add('UNION')
INTERSECTION = literals.add('INTERSECTION')
EVERYTHING = literals.add('EVERYTHING')
NOTHING = literals.add('NOTHING')
SUBSET = literals.add('SUBSET')
SUPERSET = literals.add('SUPERSET')
SET = literals.add('SET')

def _defineAxioms():
    from booleans import Forall, Exists, Implies, Iff, And, Or, inBool, BOOLEANS
    from equality import Equals
    
    # forall_{x, S} (x in S) in BOOLEANS
    _firstAxiom =\
    inSetIsInBool = Forall((x, S), In(In(x, S), BOOLEANS))
    
    # forall_{x, y} [x in Singleton(y)] = [x = y]
    singletonDef = Forall((x, y), Equals(In(x, Singleton(y)), Equals(x, y)))
    
    # forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
    unionDef = Forall((x, A, B), Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B))))
    
    # forall_{x, A, B} [x in (A intersection B)] <=> [(x in A) and (x in B)]
    intersectionDef = Forall((x, A, B), Iff(In(x, Intersection(A, B)), And(In(x, A), In(x, B))))
            
    # Composition of multi-Union, bypassing associativity for notational convenience:
    # forall_{A, B, C*} A union B union C* = A union (B union C*)
    unionComposition = Forall((A, B, multiC), Equals(Union(A, B, multiC), Union(A, Union(B, multiC))))
    
    # Composition of multi-Intersection, bypassing associativity for notational convenience:
    # forall_{A, B, C*} A intersect B intersect C* = A intersect (B intersect C*)
    intersectionComposition = Forall((A, B, multiC), Equals(Intersection(A, B, multiC), Intersection(A, Intersection(B, multiC))))
            
    # forall_{A, B} [A subset B <=> (forall_{x in A} x in B)]
    subsetDef = Forall((A, B), Iff(Subset(A, B), Forall(x, In(x, B), In(x, A))))
    
    # forall_{A, B} [A superset B <=> (forall_{x in B} x in A)]
    supersetDef = Forall((A, B), Iff(Superset(A, B), Forall(x, In(x, A), In(x, B))))
    
    # forall_{P, f, x} [x in {f(y) | P(y)}] <=> [exists_{y | P(y)} x = f(y)]
    setOfAllDef = Forall((P, f, x), Iff(In(x, SetOfAll(y, fy, conditions=Py)), Exists(y, Equals(x, fy), Py)))
    
    # forall_{A, B} [forall_{x} x in A <=> x in B] => [A=B]
    setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(In(x, A), In(x, B))), Equals(A, B)))
    
    # forall_{x} x in EVERYTHING
    allInEverything = Forall(x, In(x, EVERYTHING))

    # forall_{x} x notin EVERYTHING
    allNotInNothing = Forall(x, NotIn(x, NOTHING))
        
    return _firstAxiom, locals()

def _defineTheorems():
    from booleans import Forall, Exists, Implies, Iff, And, Or, inBool, BOOLEANS
    from equality import Equals
    
    # forall_{A, B} [A subset B => (forall_{x in A} x in B)]
    _firstTheorem=\
    unfoldSubset = Forall((A, B), Implies(Subset(A, B), Forall(x, In(x, B), In(x, A))))

    # forall_{A, B} [(forall_{x in A} x in B) => (A subset B)]
    foldSubset = Forall((A, B), Implies(Forall(x, In(x, B), In(x, A)), Subset(A, B)))

    # forall_{A, B} [A superset B => (forall_{x in B} x in A)]
    unfoldSuperset = Forall((A, B), Implies(Superset(A, B), Forall(x, In(x, A), In(x, B))))

    # forall_{A, B} [(forall_{x in B} x in A) => (A superset B)]
    foldSuperset = Forall((A, B), Implies(Forall(x, In(x, A), In(x, B)), Superset(A, B)))

    # forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
    unfoldSetOfAll = Forall((P, f, x), Implies(In(x, SetOfAll(y, fy, Py)), Exists(y, Equals(x, fy), Py)))
    
    # forall_{P, f, x} [exists_{y | P(y)} x = f(y)] => [x in {f(y) | P(y)}]
    foldSetOfAll = Forall((P, f, x), Implies(Exists(y, Equals(x, fy), Py), In(x, SetOfAll(y, fy, Py))))

    # forall_{P, x} [x in {y | P(y)}] => P(x)
    unfoldSimpleSetOfAll = Forall((P, x), Implies(In(x, SetOfAll(y, y, Py)), Px))
    
    return _firstTheorem, locals()
        
sets = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)

class In(BinaryOperation):
    def __init__(self, element, itsSet):
        BinaryOperation.__init__(self, IN, element, itsSet)
        self.element = element
        self.itsSet = itsSet
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'in'
        else:
            return '<mo>&#x2208;</mo>'

    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        return sets.inSetIsInBool.specialize({x:self.element, S:self.itsSet}).check()
    
    def unfold(self):
        '''
        From (x in S), derive and return an unfolded version.
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        return self.itsSet.unfoldElemInSet(self.element).check({self})
    
    def concludeAsFolded(self):
        '''
        Derive this folded version, x in S, from the unfolded version.
        Examples are: (x in {y}) from (x=y), (x in (A union B)) from ((x in A) or (x in B)).
        This may be extended to work for other types of sets by implementing
        the deduceElemInSet(...) method for each type [see deduceElemInSet(..) defined
        for Singleton or Union].
        '''    
        return self.itsSet.deduceElemInSet(self.element)
    
    def deriveIsInExpansion(self, expandedSet):
        '''
        From x in S, derive x in expandedSet via S subseteq expendedSet.
        '''
        #from sets import unionDef, x, A, B
        #TODO : derive x in S => x in S or x in expandingSet
        #return unionDef.specialize({x:self.element, A:self.itsSet, B:self.expandingSet}).deriveLeft()
        pass
    
    def evaluateForall(self, forallStmt):
        '''
        Given a forall statement over some set, evaluate it to TRUE or FALSE if possible
        via the set's evaluateForallInSet method.
        '''
        return self.itsSet.evaluateForallInSet(forallStmt)
    
    def unfoldForall(self, forallStmt):
        '''
        Given a forall statement over some set, unfold it if possible via the set's
        unfoldForallInSet method.
        '''
        return self.itsSet.unfoldForallInSet(forallStmt)
    
    def foldAsForall(self, forallStmt):
        '''
        Given a forall statement over some set, derive it from an unfolded version
        if possible via the set's foldAsForallInSet method.
        '''
        return self.itsSet.foldAsForallInSet(forallStmt)

Operation.registerOperation(IN, lambda operands : In(*operands))


class NotIn(BinaryOperation):
    def __init__(self, element, theSet):
        BinaryOperation.__init__(self, NOTIN, element, theSet)
        self.element = element
        self.theSet = theSet
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'not in'
        else:
            return '<mo>&#x2209;</mo>'

Operation.registerOperation(NOTIN, lambda operands : NotIn(*operands))

class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, elem)
        self.elem = elem

    def formatted(self, formatType, fenced=False):
        if formatType == STRING:
            return '{' + str(self.elem) + '}'
        else:
            return "<mfenced open='{' close='}'>" + self.elem.formatted(formatType) + '</mfenced>'

    def unfoldElemInSet(self, element):
        '''
        From [element in {y}], derive and return (element = y).
        '''
        return sets.singletonDef.specialize({x:element, y:self.elem}).deriveRightViaEquivalence()
    
    def deduceElemInSet(self, element):
        '''
        From (element = y), derive and return [element in {y}] where self represents {y}.
        '''   
        return sets.singletonDef.specialize({x:element, y:self.elem}).deriveLeftViaEquivalence()

Operation.registerOperation(SINGLETON, lambda operand : Singleton(operand))

class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, elem)
        self.elem = elem

    def __str__(self):
        return 'Complement(' + str(self.elem) + ')'

Operation.registerOperation(COMPLEMENT, lambda operand : Complement(operand))
        
class Union(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        AssociativeOperation.__init__(self, UNION, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'union'
        elif formatType == MATHML:
            return '<mo>&#x222A;</mo>'

    def deriveCompletion(self):
        '''
        derive and return S union Complement(S) = EVERYTHING or
        Complement(S) union S = EVERYTHING if this is a union of either or these forms.
        ''' 
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand       
            if leftOperand == Complement(rightOperand):
                return complementCompletion.specialize({S:leftOperand})
            elif Complement(leftOperand) == rightOperand:
                return complementCompletionReversed.specialize({S:rightOperand})

    def unfoldElemInSet(self, element):
        '''
        From [element in (A union B)], derive and return [(element in A) or (element in B)],
        where self represents (A union B). 
        '''
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand       
            return sets.unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From [(element in A) or (element in B)], derive and return [element in (A union B)]
        where self represents (A union B).
        ''' 
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand                 
            return sets.unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveLeft()

Operation.registerOperation(UNION, lambda operands : Union(*operands))

class Intersection(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        AssociativeOperation.__init__(self, INTERSECTION, *operands)
            
    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'intersection'
        elif formatType == MATHML:
            return '<mo>&#x2229;</mo>'

    def unfoldElemInSet(self, element):
        '''
        From [element in (A intersection B)], derive and return [(element in A) and (element in B)],
        where self represents (A intersection B). 
        '''
        return sets.intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From  [(element in A) and (element in B)], derive and return [element in (A intersection B)],
        where self represents (A intersection B). 
        '''
        return sets.intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveLeft()

Operation.registerOperation(INTERSECTION, lambda operands : Intersection(*operands))

class Subset(BinaryOperation):
    def __init__(self, subSet, superSet):
        BinaryOperation.__init__(self, SUBSET, subSet, superSet)
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'subset'
        else:
            return '<mo>&#x2286;</mo>'

    def unfold(self, elemInstanceVar=x):
        '''
        From A subset B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        return sets.unfoldSubset.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A subset B, from the unfolded version,
        (forall_{x in A} x in B).
        '''
        return sets.foldSubset.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

Operation.registerOperation(SUBSET, lambda operands : Subset(*operands))

class Superset(BinaryOperation):
    def __init__(self, superSet, subSet):
        BinaryOperation.__init__(self, SUPERSET, superSet, subSet)
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'superset'
        else:
            return '<mo>&#x2287;</mo>'

    def unfold(self, elemInstanceVar=x):
        '''
        From A superset B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        return sets.unfoldSuperset.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A superset B, from the unfolded version,
        (forall_{x in B} x in A).
        '''
        return sets.foldSuperset.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

Operation.registerOperation(SUPERSET, lambda operands : Superset(*operands))
 
class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, conditions=None):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, conditions)
        self.instanceElement = instanceElement

    def formatted(self, formatType, fenced=False):
        outStr = ''
        innerFenced = (len(self.condition) > 0)
        if formatType == STRING:
            outStr += '{'
            outStr += self.instanceElement.formatted(formatType, fenced=innerFenced)
            if len(self.condition) > 0:
                outStr += ' s.t. ' # such that
                if len(self.condition) == 1:
                    outStr += self.condition.formatted(formatType, fenced=True)
                else:
                    outStr += ', '.join([condition.formatted(formatType, fenced=True) for condition in self.condition])
            outStr += '}'
            if fenced: outStr += ']'
        elif formatType == MATHML:
            outStr += '<mfenced open="{" close="}">'
            outStr += '<mrow>' + self.instanceElement.formatted(formatType, fenced=innerFenced)
            if len(self.condition) > 0:
                outStr += '<mo>|</mo>'
                outStr += '<mfenced open="" close="" separators=",">'
                for condition in self.condition:
                    outStr += condition.formatted(formatType, fenced=True)
                outStr += "</mfenced>"
            outStr += '</mrow></mfenced>'
        return outStr

    def unfoldElemInSet(self, element):
        '''
        From (x in {Q(y) | P(y)}), derive and return P(x), where x is meant as the given element.
        '''
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return sets.unfoldSetOfAll.specialize({P:Lambda(self.instanceVar, self.instanceExpression), x:element}).deriveConclusion().check({PofElement})
    
    def deduceElemInSet(self, element):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return sets.foldSetOfAll.specialize({P:Lambda(self.instanceVar, self.instanceExpression), x:element}).deriveConclusion().check({PofElement})

Operation.registerOperation(SET, lambda operand : SetOfAll(operand.argument, operand.expression, operand.domainCondition))

