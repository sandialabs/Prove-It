from proveItCore import *
from genericOperations import *

sets = Context('SETS')

# set theory related literals
IN = sets.addLiteral('IN')
SINGLETON = sets.addLiteral('SINGLETON')
COMPLEMENT = sets.addLiteral('COMPLEMENT')
UNION = sets.addLiteral('UNION')
INTERSECTION = sets.addLiteral('INTERSECTION')
EVERYTHING = sets.addLiteral('EVERYTHING')
NOTHING = sets.addLiteral('NOTHING')
SUBSET = sets.addLiteral('SUBSET')
SUPERSET = sets.addLiteral('SUPERSET')
SET = sets.addLiteral('SET')

A = Variable('A')
B = Variable('B')
C = Variable('C')
P = Variable('P')
f = Variable('f')
x = Variable('x')
y = Variable('y')
X = Variable('X')
S = Variable('S')
Px = Operation(P, [x])
Py = Operation(P, [y])
fx = Operation(f, [x])
fy = Operation(f, [y])

def setAxioms():
    """
    Generates the set axioms.  Because of the interdependence of booleans, 
    equality, and sets, this is executed on demand after these have all loaded.
    """
    from booleans import BOOLEANS, Forall, Exists, Implies, Iff, And, Or
    from equality import Equals
    importVars = set(locals().keys()) | {'importVars'}
    
    # forall_{x, S} (x in S) in BOOLEANS
    inSetIsInBool = sets.stateAxiom(Forall([x, S], In(In(x, S), BOOLEANS)))
    
    # forall_{x, y} [x in Singleton(y)] = [x = y]
    singletonDef = sets.stateAxiom(Forall([x, y], Equals(In(x, Singleton(y)), Equals(x, y))))
    
    # forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
    unionDef = sets.stateAxiom(Forall([x, A, B], Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B)))))
    
    # forall_{x, A, B} [x in (A intersection B)] <=> [(x in A) and (x in B)]
    intersectionDef = sets.stateAxiom(Forall([x, A, B], Iff(In(x, Intersection(A, B)), And(In(x, A), In(x, B)))))
    
    # forall_{A, B} [A subset B <=> (forall_{x in A} x in B)]
    subsetDef = sets.stateAxiom(Forall([A, B], Iff(Subset(A, B), Forall([x], In(x, B), [In(x, A)]))))
    
    # forall_{A, B} [A superset B <=> (forall_{x in B} x in A)]
    supersetDef = sets.stateAxiom(Forall([A, B], Iff(Superset(A, B), Forall([x], In(x, A), [In(x, B)]))))
    
    # forall_{P, f, x} [x in {f(y) | P(y)}] <=> [exists_{y | P(y)} x = f(y)]
    setOfAllDef = sets.stateAxiom(Forall([P, f, x], Iff(In(x, SetOfAll([y], fy, suchThat=[Py])), Exists([y], Equals(x, fy), [Py]))))

    allLocals = dict(locals())
    return {key:allLocals[key] for key in (set(allLocals.keys()) - importVars)}

sets.axiomsOnDemand(setAxioms)

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

    def remake(self, operator, operands):
        if operator == IN and len(operands) == 2:
            return In(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
    
    def unfold(self):
        '''
        Derive an unfolded version of some (x in S) given (x in S).
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        return self.itsSet.unfoldElemInSet(self.element).check({self})
    
    def proveAsFolded(self):
        '''
        Derive this folded version, x in S, from the unfolded version.
        Examples are: (x in {y}) from (x=y), (x in (A union B)) from ((x in A) or (x in B)).
        This may be extended to work for other types of sets by implementing
        the proveElemInSet(...) method for each type [see proveElemInSet(..) defined
        for Singleton or Union].
        '''    
        return self.itsSet.proveElemInSet(self.element)
    
    def deriveIsInExpansion(self, expandedSet):
        '''
        Given x in S, derive x in expandedSet via S subseteq expendedSet.
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

class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, [elem])
        self.elem = elem

    def formatted(self, formatType, fenced=False):
        if formatType == STRING:
            return '{' + str(self.elem) + '}'
        else:
            return "<mfenced open='{' close='}'>" + self.elem.formatted(formatType) + '</mfenced>'

    def remake(self, operator, operands):
        if operator == SINGLETON and len(operands) == 1:
            return Singleton(operands[0])
        else:
            return Operation.remake(self, operator, operands)
    
    def unfoldElemInSet(self, element):
        '''
        From [element in {y}], derive and return (element = y).
        '''
        return sets.singletonDef.specialize({x:element, y:self.elem}).deriveRHSviaEquivalence()
    
    def proveElemInSet(self, element):
        '''
        From (element = y), derive and return [element in {y}] where self represents {y}.
        '''   
        return sets.singletonDef.specialize({x:element, y:self.elem}).deriveLHSviaEquivalence()

class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, [elem])
        self.elem = elem

    def __str__(self):
        return 'Complement(' + str(self.elem) + ')'

    def remake(self, operator, operands):
        if operator == COMPLEMENT and len(operands) == 1:
            return Complement(operands[0])
        else:
            return Operation.remake(self, operator, operands)
        
class Union(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do Union(A, B) to get UNION{A}{B} or 
        Union([A, B, C]) to get UNION{A}{AND{B}{C}}
        '''
        AssociativeBinaryOperation.__init__(self, UNION, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'union'
        else:
            return '<mo>&#x222A;</mo>'

    def deriveCompletion(self):
        '''
        derive and return S union Complement(S) = EVERYTHING if
        this is a union of that form.
        '''
        if self.operands[1] == Complement(self.operands[0]):
            return complementCompletion.specialize({S:self.operands[0]})

    def remake(self, operator, operands):
        if operator == UNION and len(operands) == 2:
            return Union(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
        
    def unfoldElemInSet(self, element):
        '''
        From [element in (A union B)], derive and return [(element in A) or (element in B)],
        where self represents (A union B). 
        '''
        return sets.unionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveRight()

    def proveElemInSet(self, element):
        '''
        From [(element in A) or (element in B)], derive and return [element in (A union B)]
        where self represents (A union B).
        '''   
        return sets.unionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveLeft()

class Intersection(AssociativeBinaryOperation):
    def __init__(self, operandsOrA, B=None):
        '''
        Can do Intersection(A, B) to get INTERSECTION{A}{B} or 
        Intersection([A, B, C]) to get INTERSECTION{A}{AND{B}{C}}
        '''
        AssociativeBinaryOperation.__init__(self, INTERSECTION, operandsOrA, B)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'intersection'
        else:
            return '<mo>&#x2229;</mo>'

    def remake(self, operator, operands):
        if operator == INTERSECTION and len(operands) == 2:
            return Intersection(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)

    def unfoldElemInSet(self, element):
        '''
        From [element in (A intersection B)], derive and return [(element in A) and (element in B)],
        where self represents (A intersection B). 
        '''
        return sets.intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveRight()

    def proveElemInSet(self, element):
        '''
        From  [(element in A) and (element in B)], derive and return [element in (A intersection B)],
        where self represents (A intersection B). 
        '''
        return sets.intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveLeft()


class Subset(BinaryOperation):
    def __init__(self, subSet, superSet):
        Operation.__init__(self, SUBSET, [subSet, superSet])
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'subset'
        else:
            return '<mo>&#x2286;</mo>'

    def remake(self, operator, operands):
        if operator == SUBSET and len(operands) == 2:
            return Subset(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)    

    def unfold(self, elemInstanceVar=x):
        '''
        Given A subset B, returns (forall_{x in A} x in B) derived from self.
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        return sets.unfoldSubset.specialize({A:self.operands[0], B:self.operands[1], x:elemInstanceVar}).deriveConclusion().check({self})
    
    def proveAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A subset B, from the unfolded version,
        (forall_{x in A} x in B).
        '''
        return sets.foldSubset.specialize({A:self.operands[0], B:self.operands[1], x:elemInstanceVar}).deriveConclusion()

class Superset(BinaryOperation):
    def __init__(self, superSet, subSet):
        Operation.__init__(self, SUPERSET, [superSet, subSet])
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'superset'
        else:
            return '<mo>&#x2287;</mo>'

    def remake(self, operator, operands):
        if operator == SUPERSET and len(operands) == 2:
            return Superset(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands) 
    
    def unfold(self, elemInstanceVar=x):
        '''
        Given A superset B, returns (forall_{x in B} x in A) derived from self.
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        return sets.unfoldSuperset.specialize({A:self.operands[0], B:self.operands[1], x:elemInstanceVar}).deriveConclusion().check({self})
    
    def proveAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A superset B, from the unfolded version,
        (forall_{x in B} x in A).
        '''
        return sets.foldSuperset.specialize({A:self.operands[0], B:self.operands[1], x:elemInstanceVar}).deriveConclusion()
 
class SetOfAll(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceElement, suchThat=None):
        '''
        Nest Set OperationOverInstances' for each of the given instance variables with the given 
        innermost instance element.  Each suchThat condition is applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, SET, lambda iVars, iExpr, conds: SetOfAll(iVars, iExpr, conds), instanceVars, instanceElement, suchThat)
        self.suchThat = suchThat

    def formatted(self, formatType, fenced=False):
        outStr = ''
        # go straight to the innermost instance element then list all conditions
        conditions = []
        innermostInstElem = self
        while isinstance(innermostInstElem, SetOfAll):
            conditions.append(innermostInstElem.condition)
            innermostInstElem = innermostInstElem.instanceExpression
        innerFenced = (len(conditions) > 0)
        if formatType == STRING:
            outStr += '{'
            outStr += innermostInstElem.formatted(formatType, fenced=innerFenced)
            if len(conditions) > 0:
                outStr += ' s.t. ' # such that
                if len(conditions) == 1:
                    outStr += conditions[0].formatted(formatType, fenced=True)
                else:
                    outStr += ', '.join([condition.formatted(formatType, fenced=True) for condition in conditions])
            outStr += '}'
            if fenced: outStr += ']'
        elif formatType == MATHML:
            outStr += '<mfenced open="{" close="}">'
            outStr += '<mrow>' + innermostInstElem.formatted(formatType, fenced=innerFenced)
            if len(conditions) > 0:
                outStr += '<mo>|</mo>'
                outStr += '<mfenced open="" close="" separators=",">'
                for condition in conditions:
                    outStr += condition.formatted(formatType, fenced=True)
                outStr += "</mfenced>"
            outStr += '</mrow></mfenced>'
        return outStr

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == SET:
            return SetOfAll([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)

    def unfoldElemInSet(self, element):
        '''
        From (x in {Q(y) | P(y)}), derive and return P(x), where x is meant as the given element.
        '''
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return sets.unfoldSetOfAll.specialize({P:Function(self.instanceExpression, [self.instanceVar]), x:element}).deriveConclusion().check({PofElement})
    
    def proveElemInSet(self, element):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return sets.foldSetOfAll.specialize({P:Function(self.instanceExpression, [self.instanceVar]), x:element}).deriveConclusion().check({PofElement})


"""        
class UnionOfSets(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Nest Union OperationOverInstances' for each of the given instance variables with the given 
        innermost instance expression.  The optionally provided conditions are applied as soon as the 
        instance variables they contain are introduced.  For convenience, conditions of the form 
        In(instanceVar, domain) may be provided implicitly via tuples in the instanceVars collection.  
        For example, instanceVars=[(a, A), (b, B)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, A), In(b, B)].  You can also provide multiple instance variables per domain 
        as in the following: instanceVars=[([a, b], S)] is the same as instanceVars=[a, b] with 
        conditions=[In(a, S), In(b, S)].  These implicit conditions are prepended to any explicitly 
        given conditions as this is processed.
        '''
        NestableOperationOverInstances.__init__(self, UNION, lambda iVars, iExpr, conds: UnionOfSets(iVars, iExpr, conds), instanceVars, instanceExpression, conditions)

    def __str__(self):
        return '[union_{' + str(self.instanceVar) + ' in ' + str(self.domain) + '} ' + str(self.instanceExpression) + ']'

    def remake(self, operator, instanceVar, instanceExpression, condition):
        if operator == UNION:
            return UnionOfSets([instanceVar], instanceExpression, [condition])
        else:
            return OperationOverInstances(operator, instanceVar, instanceExpression, condition)

class SetOfAll(UnionOfSets):
    def __init__(self, instanceVarsAndDomains=None, instanceElement=None, suchThat=None):
        if suchThat == None:
            UnionOfSets.__init__(self, instanceVarsAndDomains, Singleton(instanceElement))
        else:
            UnionOfSets.__init__(self, instanceVarsAndDomains, IfElse(suchThat, Singleton(instanceElement), NOTHING))

    def remake(self, operator, instanceVar, domain, instanceExpression):
        if operator == UNION and isinstance(instanceExpression, Singleton):
            return SetOfAll([(instanceVar, domain)], instanceExpression.elem)
        elif operator == UNION and isinstance(instanceExpression, IF_ELSE) and isinstance(instanceExpression.ifTrueVal, Singleton) and instanceExpression.ifFalseVal == NOTHING:
            return SetOfAll([(instanceVar, domain)], instanceExpression.ifTrueVal.elem, suchThat=instanceExpression.condition)
        else:
            return OperationOverInstances(operator, instanceVar, domain, instanceExpression)
"""        


# DERIVATIONS

# forall_{A, B} [A subset B => (forall_{x in A} x in B)]
sets.deriveOnDemand('unfoldSubset', lambda : sets.subsetDef.specialize().deriveRightImplication().generalize([A, B]).qed())

# forall_{A, B} [(forall_{x in A} x in B) => (A subset B)]
sets.deriveOnDemand('foldSubset', lambda : sets.subsetDef.specialize().deriveLeftImplication().generalize([A, B]).qed())

# forall_{A, B} [A superset B => (forall_{x in B} x in A)]
sets.deriveOnDemand('unfoldSuperset', lambda : sets.supersetDef.specialize().deriveRightImplication().generalize([A, B]).qed())

# forall_{A, B} [(forall_{x in B} x in A) => (A superset B)]
sets.deriveOnDemand('foldSuperset', lambda : sets.supersetDef.specialize().deriveLeftImplication().generalize([A, B]).qed())

# forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
sets.deriveOnDemand('unfoldSetOfAll', lambda : sets.setOfAllDef.specialize().deriveRightImplication().generalize([P, f, x]).qed())

# forall_{P, f, x} [exists_{y | P(y)} x = f(y)] => [x in {f(y) | P(y)}]
sets.deriveOnDemand('foldSetOfAll', lambda : sets.setOfAllDef.specialize().deriveLeftImplication().generalize([P, f, x]).qed())

# forall_{P, x} [x in {y | P(y)}] => P(x)
def unfoldSimpleSetOfAllDerivation():
    # forall_{P, x} [x in {y | P(y)}] => [exists_{y | P(y)} x = y]
    sets.unfoldSetOfAll.specialize({f:Function(y, [y])})
    