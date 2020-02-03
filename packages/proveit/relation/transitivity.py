"""
A TransitiveRelation is a generic base class for binary
relationships that are transitive.  Less than and greater than
relationships are examples (so are subset and superset relationships).
For example, transitivity in the "less than" context means that 
a<b and b<c implies that a<c.  The "equivalence class" 
(proveit.logic.Equals by default) is special kind of TransitiveRelation 
that is also symmetric; that is, y=x if x=y.  
proveit.logic.Equals is a TransitiveRelation, but
overloads the default methods.  The TransitiveRelation class
provides convenient automation capabilities for performing
a transitive search to conclude a new relation from known relations
using transitivity rules.  To enable this, each TransitiveRelation
needs to track to define knownLeftSides and knownRightSides as
class dictionaries; these will be populated as side effects for
each proven relation (see deriveSideEffects).  Also, the
applyTransitivity method should be appropriately implemented.
The default version handles the case when the "other" relation
is an equality (in which case, substitution may simply be performed).
"""

import itertools
from collections import deque
from proveit import Expression, Operation, OperationSequence
from proveit import defaults, USE_DEFAULTS, KnownTruth, ProofFailure
from .sorter import TransitivitySorter

class TransitiveRelation(Operation):
    r'''
    Base class for generic transitive relations.  Examples
    are <, <=, >, >= as well as subset, subseteq, superset,
    and superseteq relations.  proveit.logic.Equals is a special 
    TransitiveRelation which is also symmetric (x=y means that y=x).
    '''
    
    def __init__(self, operator, lhs, rhs):
        Operation.__init__(self,operator, (lhs, rhs))
        self.lhs = lhs
        self.rhs = rhs

    def sideEffects(self, knownTruth):
        '''
        Automatically derive the reversed form of transitive
        relations as side effects (e.g., y > x from x < y).
        Also, store known left sides and known right sides 
        in class member dictionaries: knownLeftSides, knownRightSides
        whilc will enable transitivity searches.
        '''
        if not hasattr(self.__class__, 'knownLeftSides') or not hasattr(self.__class__, 'knownRightSides'):
            raise NotImplementedError("Expressions derived from TransitiveRelation should define 'knownLeftSides' and 'knownRightSides' as class variables")
        self.__class__.knownLeftSides.setdefault(self.lhs, set()).add(knownTruth)
        self.__class__.knownRightSides.setdefault(self.rhs, set()).add(knownTruth)
        return
        yield # makes this a generator as it should be

    def conclude(self, assumptions):
        '''
        Try to conclude the TransitivityRelation using other 
        TransitivityRelations or Equals that are known to be true via transitivity.
        For example, if a<b, b=c, and c<=d are known
        truths (under the given assumptions), we can conclude that
        a<d (under these assumptions).
        '''
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        try:
            self.concludeViaTransitivity(assumptions)
        except TransitivityException as e:
            raise TransitivityException(self, assumptions, e.message) # indicate the expression we were trying to prove
        return self.prove(assumptions=assumptions, automation=False) # may need to derive a weaker form, which should occur as a side-effect
        
    def concludeViaTransitivity(self, assumptions=USE_DEFAULTS):
        from proveit.logic import Equals
        assumptions = defaults.checkedAssumptions(assumptions)
        relation = self.__class__._transitivitySearch(self.lhs, self.rhs, assumptions=assumptions).expr
        if relation.__class__ != self.__class__:
            if self.__class__ == self.__class__._checkedWeakRelationClass():
                if relation.__class__ == self.__class__._checkedStrongRelationClass():
                    return relation.deriveRelaxed()
                elif relation.__class__ == Equals:
                    # Derive a weaker relation via the strong relation 
                    # of equality:
                    return self.concludeViaEquality(assumptions)
            msg = ("Not able to conclude the desired relation of %s"
                    " from the proven relation of %s."
                    %(str(self), str(relation)))
            raise TransitivityException(self, assumptions, msg)
        return relation
    
    @classmethod
    def _RelationClasses(cls):
        '''
        Return the strong and weak relation classes.
        '''
        return (cls._checkedStrongRelationClass(), 
                    cls._checkedWeakRelationClass())

    @classmethod
    def knownRelationsFromLeft(RelationClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, right-hand-side) pairs for this
        transitive relationship (or equality) that involve the given expression on 
        the left side and are known to be true under the given assumptions.
        Equality relations will always be yielded first.
        Strong relations will be yielded next.
        Weak relations will only be yielded if this is a weak
        relation class.
        '''
        equiv_class = RelationClass.EquivalenceClass()
        # equivalence relationships are strongest and should come first.
        equiv_left_relations = equiv_class.knownRelationsFromLeft(expr, assumptionsSet)
        for (knownTruth, otherExpr) in equiv_left_relations:
            if expr != otherExpr: # exclude reflexive equations -- they don't count
                yield (knownTruth, otherExpr)
        if RelationClass is not equiv_class:
            relation_classes = RelationClass._RelationClasses()
            # stronger then weaker relations
            for Relation in relation_classes:
                for knownTruth in list(Relation.knownLeftSides.get(expr, [])):
                    if knownTruth.isSufficient(assumptionsSet):
                        yield (knownTruth, knownTruth.rhs)
                
    @classmethod
    def knownRelationsFromRight(RelationClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, left-hand-side) pairs for this
        transitivie relationship (or equality) that involve the given expression on 
        the right side and are known to be true under the given assumptions.
        Equality relations will always be yielded first.
        Strong relations will be yielded next.
        Weak relations will only be yielded if this is a weak
        relation class.
        '''
        equiv_class = RelationClass.EquivalenceClass()
        # equivalence relationships are strongest and should come first.
        equiv_right_relations = equiv_class.knownRelationsFromRight(expr, assumptionsSet)
        for (knownTruth, otherExpr) in equiv_right_relations:
            if expr != otherExpr: # exclude reflexive equations -- they don't count
                yield (knownTruth, otherExpr)
        if RelationClass is not equiv_class:
            relation_classes = RelationClass._RelationClasses()
            # stronger then weaker relations
            for Relation in relation_classes:
                for knownTruth in list(Relation.knownRightSides.get(expr, [])):
                    if knownTruth.isSufficient(assumptionsSet):
                        yield (knownTruth, knownTruth.lhs)
    
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply transitivity to derive a new relation from 'self' and 'other'.
        For example, from self:a<b, other:b=c, derive a<c.
        This must be implemented for the different types of transitive
        relations.  This default version handles the case where
        'other' is an equality (as in the above example.
        '''
        equiv_class = self.EquivalenceClass()
        #print 'apply transitivity', self, other
        assumptions = defaults.checkedAssumptions(assumptions)        
        if isinstance(other,equiv_class):
            if other.lhs in (self.lhs, self.rhs):
                subrule = other.subRightSideInto
                commonExpr = other.lhs
            elif other.rhs in (self.lhs, self.rhs):
                subrule = other.subLeftSideInto
                commonExpr = other.rhs
            else:
                raise ValueError("Equality does not involve either side of inequality!")
            if commonExpr == self.lhs:
                # replace the lhs of self with its counterpart from the "other" equality.
                return subrule(self.innerExpr().lhs, assumptions=assumptions)
            elif commonExpr == self.rhs:
                # replace the rhs of self with its counterpart from the "other" equality.
                return subrule(self.innerExpr().rhs, assumptions=assumptions)
        raise NotImplementedError('Must implement applyTransitivity appropriately for each kind of TransitiveRelation')

    @staticmethod
    def applyTransitivities(chain, assumptions=USE_DEFAULTS):
        '''
        Apply transitvity rules on a list of relations in the given chain
        to proof the relation over the chain end points.
        Each element of the chain must be a KnownTruth object that represents
        a proven relation for which transitivity rules may be applied via
        an 'applyTransitivity' method (such as a KnownTruth for a proven
        Equals statement).  The chain must "connect" in the sense that any
        two neighbors in the chain can be joined vie applyTransitivity.
        The transitivity rule will be applied left to right.
        '''
        assumptions = defaults.checkedAssumptions(assumptions)
        if len(chain) == 0:
            raise TransitivityException(None, assumptions, 'Empty transitivity relation train')
        if not all(isinstance(element, KnownTruth) for element in chain):
            raise TypeError('Expecting chain elements to be KnownTruth objects')
        while len(chain) >= 2:
            first = chain.pop(0)
            second = chain.pop(0)
            new_relation = first.applyTransitivity(second, assumptions=assumptions)
            if not isinstance(new_relation, KnownTruth):
                raise TypeError("applyTransitivity should return a KnownTruth, not %s"%new_relation)
            chain.insert(0, new_relation)
        return chain[0] # we are done

    @staticmethod
    def EquivalenceClass():
        from proveit.logic import Equals
        return Equals
    
    @staticmethod
    def WeakRelationClass():
        raise NotImplementedError("The Expression class for the weak form of the relation (that include equality as a possibility) should be returned")

    @staticmethod
    def StrongRelationClass():
        raise NotImplementedError("The Expression class for the strong form of the relation (that excludes equality as a possibility) should be returned")

    @classmethod
    def _checkedWeakRelationClass(RelationClass):
        equiv_class = RelationClass.EquivalenceClass()
        if RelationClass==equiv_class: return equiv_class # ("equal to" or "equal to" is just "equal to")
        try:
            Relation = RelationClass.WeakRelationClass()
        except NotImplementedError:
            raise NotImplementedError("The Expression class for the weak form %s (that include equality as a possibility) should be returned"%str(RelationClass))
        assert issubclass(Relation, TransitiveRelation), "WeakRelationClass() should return a sub-class of TransitiveRelation"
        return Relation

    @classmethod
    def _checkedStrongRelationClass(RelationClass):
        try:
            Relation = RelationClass.StrongRelationClass()
        except NotImplementedError:
            raise NotImplementedError("The Expression class for the strong form %s (that excludes equality as a possibility) should be returned"%str(RelationClass))            
        assert issubclass(Relation, TransitiveRelation), "StrongRelationClass() should return a sub-class of TransitiveRelation"
        return Relation

    @staticmethod
    def SequenceClass():
        raise NotImplementedError("The Expression class for the transitive relation sequence should be returned")

    @classmethod
    def makeSequenceOrRelation(self, *relations):
        if len(relations)==1:
            return relations[0] # only 1 relation
        Sequence = self.SequenceClass()
        assert issubclass(Sequence, TransitiveSequence), "SequenceClass() should return a sub-class TransitiveSequence"
        operators = [relation.operator for relation in relations]
        operands = [relation.lhs for relation in relations] + [relations[-1].rhs]
        alt_operands = [relations[0].lhs] + [relation.rhs for relation in relations]
        if operands != alt_operands:
            raise TypeError("The relations do not have the expected operands in common to form a sequence")
        return Sequence(operators, operands)
    
    @classmethod
    def sorted_items(cls, items, reorder=True, assumptions=USE_DEFAULTS):
        '''
        Return the given items in sorted order with respect to this 
        TransitivityRelation class (cls) under the given assumptions
        using known transitive relations.
        If reorder is False, raise a TransitivityException if the
        items are not in sorted order as provided.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        from proveit.number import isLiteralInt
        assumptions = defaults.checkedAssumptions(assumptions)
        if all(isLiteralInt(item) for item in items):
            # All the items are integers.  Use efficient n log(n) sorting to
            # get them in the proper order and then use fixedTransitivitySort
            # to efficiently prove this order.
            items = sorted(items, key = lambda item : item.asInt())
            reorder = False 
        if reorder:
            sorter = TransitivitySorter(cls, items, assumptions=assumptions)
            return list(sorter)
        else:
            return cls._fixedTransitivitySort(items, assumptions=assumptions).operands
    
    @classmethod
    def sort(cls, items, reorder=True, assumptions=USE_DEFAULTS):
        '''
        Return the proven Sequence, a known truth for an expression 
        of type cls.SequenceClass(), representing the sorted sequence
        according to the cls.sorted_items method.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        automation = True
        assumptions = defaults.checkedAssumptions(assumptions)
        if reorder:
            items = cls.sorted_items(items, reorder, assumptions)
            #print("sorted", items)
            automation = False # Direct relations already proven.
        return cls._fixedTransitivitySort(items, assumptions=assumptions, 
                                          automation=automation)
    
    @classmethod
    def mergesorted_items(cls, item_iterators, 
                          assumptions=USE_DEFAULTS,
                          skip_exact_reps=False,
                          skip_equiv_reps=False,
                          requirements=None):
        '''
        Given a list of Expression item iterators, with each generator 
        yielding items in sorted order, yield every item (from all the
        generators) in sorted order.  If skip_exact_reps is True,
        only yield the first of an 'item' that is repeated
        exactly (equal Expressions).  If skip_equiv_reps is True,
        only yield the first of an 'item' that is repeated via
        a known equivalence.  Passes back requirements (if provided)
        that are the specific merger relations.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        assumptions = defaults.checkedAssumptions(assumptions)
        
        # item_iterators may be actual iterators or something that
        # can produce an iterator. Convert them all to actual iterators.
        for k, iterator in enumerate(item_iterators):
            try:
                # Try to convert to an actual iterator.
                item_iterators[k] = iter(iterator)
            except:
                pass # Assume it is already an actual iterator.
                
        # Start with the first item from each generator and track
        # the generator(s) for each item so we no where to get the
        # item(s) to be added after yielding the "next" sorted item.
        first_items = []
        front_item_to_iterators = dict()
        for iterator in item_iterators:
            try:
                item = next(iterator)
                first_items.append(item)
                front_item_to_iterators.setdefault(item, []).append(iterator)
            except StopIteration:
                pass
        
        if requirements is None:
            requirements = []
        
        # Create a TransitivitySorter.
        sorter = TransitivitySorter(cls, first_items, assumptions=assumptions,
                                    skip_exact_reps=skip_exact_reps,
                                    skip_equiv_reps=skip_equiv_reps)
        # Yield items in sorted order from the TransitivitySorter,
        # add to the TransitivitySorter as new items become "exposed",
        # and keep front_item_to_iterators updated.
        prev_item = None
        prev_iters = None
        for next_item in sorter:
            yield next_item # Yield the next item.
            if next_item not in front_item_to_iterators:
                prev_item = next_item
                prev_iters = set()
                continue
            # Add newly "exposed" items and update 
            # front_item_to_iterators.
            iterators = front_item_to_iterators.pop(next_item)
            if prev_item is not None and prev_iters.isdisjoint(iterators):
                # next_item and prev_item are in different iterators,
                # so their relationship is important for establishing
                # the sorted order of the merger. 
                requirement = cls._transitivitySearch(prev_item, next_item, 
                                                      assumptions=assumptions, 
                                                      automation=False)
                requirements.append(requirement)
            for iterator in iterators:
                try:
                    item_to_add = next(iterator)
                    # Add "exposed" item.
                    sorter.add(item_to_add)
                    # Update front_item_to_iterators.
                    front_item_to_iterators.setdefault(item_to_add, 
                                                       []).append(iterator)
                except StopIteration:
                    pass # Nothing more from this generator.
            prev_item = next_item
            prev_iters = set(iterators)
    
    @classmethod
    def mergesort(cls, item_iterators, assumptions=USE_DEFAULTS,
                  skip_exact_reps=False, skip_equiv_reps=False,
                  requirements=None):
        '''
        Return the proven Sequence, a known truth for an expression 
        of type cls.SequenceClass(), representing the sorted sequence
        according to the cls.mergesorted_items method.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        assumptions = defaults.checkedAssumptions(assumptions)
        items = cls.mergesorted_items(item_iterators, assumptions,
                                      skip_exact_reps, skip_equiv_reps,
                                      requirements)
        items = list(items)
        #print("merge sorted", items)
        return cls._fixedTransitivitySort(items, assumptions=assumptions,
                                           automation=False)        
    
    @classmethod
    def insertion_point(cls, sorted_items, item_to_insert, 
                        equiv_group_pos='any',
                        assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return the position to insert the "item to insert" into the 
        sorted items to maintain the sorted order (according to
        the TransitivityRelation class cls).  The sorted_items should
        be provably sorted, with relations between consecutive items
        that are KnownTruths.  
        
        If equiv_group_pos is 'first', the insertion point will be one
        that would place he "item to insert" prior to any equivalent 
        items; if equiv_group_pos is 'last', the insertion point will be
        one that would place the "item to insert" after any equivalent
        items.  If it is 'first&last', both insertion points are
        returned as a tuple pair (first, last).
        The default of equiv_group_pos='any' will result in
        an arbitrary position relative to equivalent items.
        ''' 
        equiv_class = cls.EquivalenceClass()
        assumptions = defaults.checkedAssumptions(assumptions)
        if item_to_insert in sorted_items:
            point = sorted_items.index(item_to_insert)
        else:
            item_iterators = [sorted_items, [item_to_insert]]
            # Don't skip equivalent or exact representations because
            # we don't want the insertion point index to be thrown
            # off and we need to make sure the 'item_to_insert' is 
            # included:
            skip_exact_reps = skip_equiv_reps = False
            # And don't skip exact representations
            for k, item in enumerate(cls.mergesorted_items(item_iterators,
                                                            assumptions,
                                                            skip_exact_reps,
                                                            skip_equiv_reps,
                                                            requirements)):
                if item==item_to_insert:
                    point = k
        
        # If equiv_group_pos is 'first' or 'last', we need to make sure
        # we get the insertion point in the right spot with respect to
        # equivalent items.
        
        orig_point = point
        equiv_item = item_to_insert
        if equiv_group_pos=='first' or equiv_group_pos=='first&last':
            while point>1:
                prev_point = point-1
                if item_to_insert==sorted_items[prev_point]:
                    point -= 1
                    continue
                item1, item2 = sorted_items[prev_point], equiv_item
                try:
                    relation = \
                        cls._transitivitySearch(item1, item2, assumptions,
                                                automation=False)
                except ProofFailure:
                    msg = ("Unknown %s relationship between %s and %s"
                            %(cls, item1, item2))
                    raise TransitivityException(None, assumptions, msg)
                if isinstance(relation.expr, equiv_class):
                    equiv_item = sorted_items[prev_point]
                    point -= 1
                else:
                    break
            first = point
                
        if equiv_group_pos=='last' or equiv_group_pos=='first&last':
            point = orig_point
            while point<len(sorted_items):
                if item_to_insert==sorted_items[point]:
                    point += 1
                    continue
                item1, item2 = equiv_item, sorted_items[point]
                try:
                    relation = \
                        cls._transitivitySearch(item1, item2, assumptions,
                                                automation=False)
                except ProofFailure:
                    msg = ("Unknown %s relationship between %s and %s"
                            %(cls, item1, item2))
                    raise TransitivityException(None, assumptions, msg)
                if isinstance(relation.expr, equiv_class):
                    equiv_item = sorted_items[point]
                    point += 1
                else:
                    break
            last = point
        
        if equiv_group_pos=='first&last':
            return (first, last)
        return point
                
    
    @classmethod
    def _transitivitySearch(cls, leftItem, rightItem, 
                            assumptions, automation=True):
        '''
        Performs a breadth-first, bidirectional (meet in the middle) search attempting
        to prove a relation between leftItem and rightItem according to the RelationClass
        by applying transitivity derivations.
        If successful, the approprate KnownTruth relating these items (in weak or strong
        form as can be determined) is returned; otherwise a TransitivityException is raised.
        '''
        equiv_class = cls.EquivalenceClass()
        
        #  Check if the relation is already known directly:
        if leftItem==rightItem:
            # Items are the exact same, so they are equal.
            return equiv_class(leftItem, rightItem).prove()
        try:
            # Try the strong relation first.
            StrongClass = cls._checkedStrongRelationClass()
            relation = StrongClass(leftItem, rightItem)
            return relation.prove(assumptions=assumptions, automation=False)
        except (ProofFailure, NotImplementedError):
            # Try equality.
            try:                    
                # Maybe the equality is known.
                relation = equiv_class(leftItem, rightItem)
                return relation.prove(assumptions=assumptions,
                                        automation=False)
            except ProofFailure:
                pass
            # Try the weak relation if cls is weak.
            if cls == cls._checkedWeakRelationClass():
                try:
                    # Maybe the weak relation is known.
                    WeakClass = cls._checkedWeakRelationClass()
                    relation = WeakClass(leftItem, rightItem)
                    return relation.prove(assumptions=assumptions,
                                            automation=False)
                except (ProofFailure, NotImplementedError):
                    pass

        if not automation:
            relation = cls(leftItem, rightItem)
            msg = ('No proof found via applying transitivity amongst'
                   ' known proven relations.')
            raise TransitivityException(relation, assumptions, msg)
        
        sorter = TransitivitySorter(cls, [leftItem, rightItem], 
                                    assumptions=assumptions,
                                    skip_exact_reps=False, 
                                    skip_equiv_reps=False,
                                    presorted_pair=True)
        list(sorter) # should prove desired relation
        # Return the proven relation.
        return cls._transitivitySearch(leftItem, rightItem,
                                        assumptions, automation=False)
    
    @classmethod
    def _fixedTransitivitySort(cls, items, assumptions, 
                               automation=True):
        '''
        Check that the given items are in sorted order, returning the 
        sorted sequence if they are or raising a TransitivityException
        if they are not.  If automation is False, don't generate
        new relations through transitivities; assume that we already
        have the necessary direct relationships proven.
        '''
        items_list = list(items) # in case the items are a non-indexable iterable
        relations = []
        for item1, item2 in zip(items_list[:-1], items_list[1:]):
            relations.append(cls._transitivitySearch(item1, item2, 
                                                     assumptions=assumptions, 
                                                     automation=automation))
        if len(relations)==1:
            return relations[0]
        return cls.makeSequenceOrRelation(*relations)


class TransitiveSequence(OperationSequence):
    '''
    Base clase for Operation Expressions that represent a sequence of transitive relationships.
    For example, w < x = y <= z.  As shown in this example, the relations may include weak, 
    strong, and/or equality.  It may not mix different types of relations.  The type of relation
    is dictated by the RelationClass() class method defined in the derived class.
    '''
    
    def __init__(self, operators, operands, doMinSizeCheck=True):
        if doMinSizeCheck and len(operators) < 2:
            raise ValueError("Do not use a TransitiveSequence for fewer than two relationship (it is unnecessary)")
        if len(operators)+1 != len(operands):
            raise ValueError("There must be one more operand than operator in a TransitiveSequence")
        relation_class = self.__class__.RelationClass()
        assert issubclass(relation_class, TransitiveRelation), "The Relation class of a TransitiveSequence should be a TransitiveRelation"
        equiv_class = relation_class.EquivalenceClass()
        relation_operators = (relation_class.WeakRelationClass()._operator_, 
                              relation_class.StrongRelationClass()._operator_, 
                              equiv_class._operator_)
        for operator in operators:
            if operator not in relation_operators:
                raise TypeError("Operators of TransitiveSequence should be %s, %s, or %s"%tuple(str(relation_operator) for relation_operator in relation_operators))
        Operation.__init__(self, operators, operands)
    
    @classmethod
    def RelationClass(SequenceClass):
        raise NotImplementedError("Must identify the Relation class for the sequence which should be a TransitiveRelation class")
    
    def insert(self, item, assumptions=USE_DEFAULTS):
        assumptions = defaults.checkedAssumptions(assumptions)
        Relation = self.__class__.RelationClass()
        return Relation._transitivityInsert(self, self.operators, self.operands, item, assumptions)


def makeSequenceOrRelation(TransitiveSequenceClass, operators, operands):
    '''
    Create a TransitiveSequence of some kind with the given operators or operands,
    or create an appropriate degenerate Expression when there are fewer than two operators.
    '''
    if len(operators)+1 != len(operands):
        raise ValueError("Expecting one more operand than operators")
    if len(operators)==0:
        return operands[0]
    if len(operators)==1:
        return Operation.operationClassOfOperator[operators[0]](*operands)
    return TransitiveSequenceClass(operators, operands)

class TransitivityException(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)
 
