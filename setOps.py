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
    
    def deriveIsInExpansion(self, expandedSet):
        '''
        Given x in S, derive x in expandedSet via S subseteq expendedSet.
        '''
        #from sets import unionDef, x, A, B
        #TODO : derive x in S => x in S or x in expandingSet
        #return unionDef.specialize({x:self.element, A:self.itsSet, B:self.expandingSet}).deriveLeft()
        pass

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

    def unfold(self, elemInstanceVar=None):
        '''
        Given A subset B, returns (forall_{x} x in A => x in B) derived from self.
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        from sets import subsetDef, A, B, x
        unfolded = subsetDef.specialize({A:self.operands[0], B:self.operands[1]}).deriveConclusion()
        if elemInstanceVar != None:
            unfolded = unfolded.relabeled({x:elemInstanceVar})
        return unfolded

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
    
    def unfold(self, elemInstanceVar=None):
        '''
        Given A superset B, returns (forall_{x} x in B => x in A) derived from self.
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        from sets import supersetDef, A, B, x
        unfolded = supersetDef.specialize({A:self.operands[0], B:self.operands[1]}).deriveConclusion()
        if elemInstanceVar != None:
            unfolded = unfolded.relabeled({x:elemInstanceVar})
        return unfolded
 
class SetOfAll(NestableOperationOverInstances):
    def __init__(self, instanceVars, instanceElement, suchThat=None):
        '''
        Nest Set OperationOverInstances' for each of the given instance variables with the given 
        innermost instance element.  Each suchThat condition is applied as soon as the 
        instance variables they contain are introduced.
        '''
        NestableOperationOverInstances.__init__(self, SET, lambda iVars, iExpr, conds: SetOfAll(iVars, iExpr, conds), instanceVars, instanceElement, suchThat)

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
