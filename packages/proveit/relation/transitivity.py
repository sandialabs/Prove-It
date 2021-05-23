"""
A TransitiveRelation is a generic base class for binary
relationships that are transitive.  Less than and greater than
relationships are examples (so are subset and superset relationships).
For example, transitivity in the "less than" theory means that
a<b and b<c implies that a<c.  The "equivalence class"
(proveit.logic.Equals by default) is special kind of TransitiveRelation
that is also symmetric; that is, y=x if x=y.
proveit.logic.Equals is a TransitiveRelation, but
overloads the default methods.  The TransitiveRelation class
provides convenient automation capabilities for performing
a transitive search to conclude a new relation from known relations
using transitivity rules.  To enable this, each TransitiveRelation
needs to track to define known_left_sides and known_right_sides as
class dictionaries; these will be populated as side effects for
each proven relation (see derive_side_effects).  Also, the
apply_transitivity method should be appropriately implemented.
The default version handles the case when the "other" relation
is an equality (in which case, substitution may simply be performed).
"""

from proveit import defaults, USE_DEFAULTS, Judgment, ProofFailure
from proveit.decorators import prover
from .sorter import TransitivitySorter
from .relation import Relation


class TransitiveRelation(Relation):
    r'''
    Base class for generic transitive relations.  Examples
    are <, <=, >, >= as well as subset, subseteq, superset,
    and superseteq relations.  proveit.logic.Equals is a special
    TransitiveRelation which is also symmetric (x=y means that y=x).
    '''

    def __init__(self, operator, normal_lhs, normal_rhs, *, styles):
        Relation.__init__(self,operator, normal_lhs, normal_rhs, styles=styles)
    
    def side_effects(self, judgment):
        '''
        Automatically derive the reversed form of transitive
        relations as side effects (e.g., y > x from x < y).
        Also, store known left sides and known right sides
        in class member dictionaries: known_left_sides, known_right_sides
        whilc will enable transitivity searches.
        '''
        if (not hasattr(self.__class__, 'known_left_sides') 
                or not hasattr(self.__class__, 'known_right_sides')):
            raise NotImplementedError(
                "Expressions derived from TransitiveRelation should define "
                "'known_left_sides' and 'known_right_sides' as class "
                "variables")
        self.__class__.known_left_sides.setdefault(
            self.normal_lhs, set()).add(judgment)
        self.__class__.known_right_sides.setdefault(
            self.normal_rhs, set()).add(judgment)
        return
        yield  # makes this a generator as it should be

    @prover
    def conclude(self, **defaults_config):
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
            return self.conclude_via_transitivity()
        except TransitivityException as e:
            # indicate the expression we were trying to prove
            raise TransitivityException(self, defaults.assumptions, e.message)

    @prover
    def conclude_via_transitivity(self, **defaults_config):
        from proveit.logic import Equals
        proven_relation = self.__class__._transitivity_search(
            self.normal_lhs, self.normal_rhs)
        relation = proven_relation.expr
        if relation.__class__ != self.__class__:
            if self.__class__ == self.__class__._checkedWeakRelationClass():
                if relation.__class__ == self.__class__._checkedStrongRelationClass():
                    return relation.derive_relaxed()
                elif relation.__class__ == Equals:
                    # Derive a weaker relation via the strong relation
                    # of equality:
                    return self.conclude_via_equality()
            msg = ("Not able to conclude the desired relation of %s"
                   " from the proven relation of %s."
                   % (str(self), str(relation)))
            raise TransitivityException(self, defaults.assumptions, msg)
        return proven_relation.with_matching_style(self)

    @classmethod
    def _RelationClasses(cls):
        '''
        Return the strong and weak relation classes.
        '''
        return (cls._checkedStrongRelationClass(),
                cls._checkedWeakRelationClass())

    @classmethod
    def known_relations_from_left(RelationClass, expr, assumptions_set):
        '''
        Yield (Judgment, right-hand-side) pairs for this
        transitive relationship (or equality) that involve the given expression on
        the left side and are known to be true under the given assumptions.
        Equality relations will always be yielded first.
        Strong relations will be yielded next.
        Weak relations will only be yielded if this is a weak
        relation class.
        '''
        equiv_class = RelationClass.EquivalenceClass()
        # equivalence relationships are strongest and should come first.
        equiv_left_relations = equiv_class.known_relations_from_left(
            expr, assumptions_set)
        for (judgment, other_expr) in equiv_left_relations:
            if expr != other_expr:  # exclude reflexive equations -- they don't count
                yield (judgment, other_expr)
        if RelationClass is not equiv_class:
            relation_classes = RelationClass._RelationClasses()
            # stronger then weaker relations
            for _Relation in relation_classes:
                for judgment in list(_Relation.known_left_sides.get(expr, [])):
                    if judgment.is_applicable(assumptions_set):
                        yield (judgment, judgment.normal_rhs)

    @classmethod
    def known_relations_from_right(RelationClass, expr, assumptions_set):
        '''
        Yield (Judgment, left-hand-side) pairs for this
        transitivie relationship (or equality) that involve the given expression on
        the right side and are known to be true under the given assumptions.
        Equality relations will always be yielded first.
        Strong relations will be yielded next.
        Weak relations will only be yielded if this is a weak
        relation class.
        '''
        equiv_class = RelationClass.EquivalenceClass()
        # equivalence relationships are strongest and should come first.
        equiv_right_relations = equiv_class.known_relations_from_right(
            expr, assumptions_set)
        for (judgment, other_expr) in equiv_right_relations:
            if expr != other_expr:  # exclude reflexive equations -- they don't count
                yield (judgment, other_expr)
        if RelationClass is not equiv_class:
            relation_classes = RelationClass._RelationClasses()
            # stronger then weaker relations
            for _Relation in relation_classes:
                for judgment in list(_Relation.known_right_sides.get(expr, [])):
                    if judgment.is_applicable(assumptions_set):
                        yield (judgment, judgment.normal_lhs)

    @prover
    def apply_transitivity(self, other, **defaults_config):
        '''
        Apply transitivity to derive a new relation from 
        'self' and 'other'.
        For example, from self:a<b, other:b=c, derive a<c.
        This must be implemented for the different types of transitive
        relations.  This default version handles the case where
        'other' is an Equals expression.
        '''
        from proveit.logic import Equals
        # print 'apply transitivity', self, other
        if isinstance(other, Equals):
            if other.normal_lhs in (self.normal_lhs, self.normal_rhs):
                subrule = other.sub_right_side_into
                common_expr = other.normal_lhs
            elif other.normal_rhs in (self.normal_lhs, self.normal_rhs):
                subrule = other.sub_left_side_into
                common_expr = other.normal_rhs
            else:
                raise ValueError(
                    "Equality does not involve either side of inequality!")
            if common_expr == self.normal_lhs:
                # replace the normal_lhs of self with its counterpart 
                # from the "other" equality.
                return subrule(self.inner_expr().normal_lhs)
            elif common_expr == self.normal_rhs:
                # replace the normal_rhs of self with its counterpart 
                # from the "other" equality.
                return subrule(self.inner_expr().normal_rhs)
        raise NotImplementedError(
            'Must implement apply_transitivity appropriately for each '
            'kind of TransitiveRelation')

    @staticmethod
    @prover
    def apply_transitivities(chain, **defaults_config):
        '''
        Apply transitvity rules on a list of relations in the given chain
        to proof the relation over the chain end points.
        Each element of the chain must be a Judgment object that represents
        a proven relation for which transitivity rules may be applied via
        an 'apply_transitivity' method (such as a Judgment for a proven
        Equals statement).  The chain must "connect" in the sense that any
        two neighbors in the chain can be joined vie apply_transitivity.
        The transitivity rule will be applied left to right.
        '''
        if len(chain) == 0:
            raise TransitivityException(
                None, defaults.assumptions, 'Empty transitivity relation train')
        if not all(isinstance(element, Judgment) for element in chain):
            raise TypeError('Expecting chain elements to be Judgment objects')
        while len(chain) >= 2:
            first = chain.pop(0)
            second = chain.pop(0)
            new_relation = first.apply_transitivity(second)
            if not isinstance(new_relation, Judgment):
                raise TypeError(
                    "apply_transitivity should return a Judgment, not %s" %
                    new_relation)
            chain.insert(0, new_relation)
        return chain[0]  # we are done

    @staticmethod
    def EquivalenceClass():
        from proveit.logic import Equals
        return Equals

    @staticmethod
    def WeakRelationClass():
        raise NotImplementedError(
            "The Expression class for the weak form of the relation (that include equality as a possibility) should be returned")

    @staticmethod
    def StrongRelationClass():
        raise NotImplementedError(
            "The Expression class for the strong form of the relation (that excludes equality as a possibility) should be returned")

    @classmethod
    def _checkedWeakRelationClass(RelationClass):
        equiv_class = RelationClass.EquivalenceClass()
        if RelationClass == equiv_class:
            return equiv_class  # ("equal to" or "equal to" is just "equal to")
        try:
            Relation = RelationClass.WeakRelationClass()
        except NotImplementedError:
            raise NotImplementedError(
                "The Expression class for the weak form %s (that include equality as a possibility) should be returned" %
                str(RelationClass))
        assert issubclass(
            Relation, TransitiveRelation), "WeakRelationClass() should return a sub-class of TransitiveRelation"
        return Relation

    @classmethod
    def _checkedStrongRelationClass(RelationClass):
        try:
            Relation = RelationClass.StrongRelationClass()
        except NotImplementedError:
            raise NotImplementedError(
                "The Expression class for the strong form %s (that excludes equality as a possibility) should be returned" %
                str(RelationClass))
        assert issubclass(
            Relation, TransitiveRelation), "StrongRelationClass() should return a sub-class of TransitiveRelation"
        return Relation
    
    @classmethod
    def sorted_items(cls, items, reorder=True, **defaults_config):
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
        from proveit.numbers import is_literal_int
        if all(is_literal_int(item) for item in items):
            # All the items are integers.  Use efficient n log(n) sorting to
            # get them in the proper order and then use fixed_transitivity_sort
            # to efficiently prove this order.
            items = sorted(items, key=lambda item: item.as_int())
            reorder = False
        if reorder:
            sorter = TransitivitySorter(cls, items, 
                                        assumptions=defaults.assumptions)
            return list(sorter)
        else:
            return cls._fixed_transitivity_sort(items).operands

    @classmethod
    @prover
    def sort(cls, items, reorder=True, **defaults_config):
        '''
        Return the proven total ordering (conjunction of relations
        presented in the total ordering style) representing the sorted 
        sequence according to the cls.sorted_items method.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        automation = True
        if reorder:
            items = cls.sorted_items(items, reorder)
            #print("sorted", items)
            automation = False  # Direct relations already proven.
        return cls._fixed_transitivity_sort(items, automation=automation)

    @classmethod
    def mergesorted_items(cls, item_iterators,
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
        # item_iterators may be actual iterators or something that
        # can produce an iterator. Convert them all to actual iterators.
        for k, iterator in enumerate(item_iterators):
            try:
                # Try to convert to an actual iterator.
                item_iterators[k] = iter(iterator)
            except BaseException:
                pass  # Assume it is already an actual iterator.

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
        sorter = TransitivitySorter(cls, first_items, 
                                    assumptions=defaults.assumptions,
                                    skip_exact_reps=skip_exact_reps,
                                    skip_equiv_reps=skip_equiv_reps)
        # Yield items in sorted order from the TransitivitySorter,
        # add to the TransitivitySorter as new items become "exposed",
        # and keep front_item_to_iterators updated.
        prev_item = None
        prev_iters = None
        for next_item in sorter:
            yield next_item  # Yield the next item.
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
                requirement = cls._transitivity_search(prev_item, next_item,
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
                    pass  # Nothing more from this generator.
            prev_item = next_item
            prev_iters = set(iterators)

    @classmethod
    @prover
    def mergesort(cls, item_iterators, skip_exact_reps=False, 
                  skip_equiv_reps=False, requirements=None,
                  **defaults_config):
        '''
        Return the proven Sequence, a judgment for an expression
        of type cls.SequenceClass(), representing the sorted sequence
        according to the cls.mergesorted_items method.
        Weak relations (e.g., <=) are only considered when calling
        this method on a weak relation class (otherwise, only
        equality and strong relations are used in the sorting).
        '''
        items = cls.mergesorted_items(item_iterators,
                                      skip_exact_reps, skip_equiv_reps,
                                      requirements)
        items = list(items)
        #print("merge sorted", items)
        return cls._fixed_transitivity_sort(items, automation=False)

    @classmethod
    def insertion_point(cls, sorted_items, item_to_insert,
                        equiv_group_pos='any', requirements=None):
        '''
        Return the position to insert the "item to insert" into the
        sorted items to maintain the sorted order (according to
        the TransitivityRelation class cls).  The sorted_items should
        be provably sorted, with relations between consecutive items
        that are Judgments.

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
                                                           skip_exact_reps,
                                                           skip_equiv_reps,
                                                           requirements)):
                if item == item_to_insert:
                    point = k

        # If equiv_group_pos is 'first' or 'last', we need to make sure
        # we get the insertion point in the right spot with respect to
        # equivalent items.

        orig_point = point
        equiv_item = item_to_insert
        if equiv_group_pos == 'first' or equiv_group_pos == 'first&last':
            while point > 1:
                prev_point = point - 1
                if item_to_insert == sorted_items[prev_point]:
                    point -= 1
                    continue
                item1, item2 = sorted_items[prev_point], equiv_item
                try:
                    relation = \
                        cls._transitivity_aearch(item1, item2,
                                                automation=False)
                except ProofFailure:
                    msg = ("Unknown %s relationship between %s and %s"
                           % (cls, item1, item2))
                    raise TransitivityException(None, defaults.assumptions, msg)
                if isinstance(relation.expr, equiv_class):
                    equiv_item = sorted_items[prev_point]
                    point -= 1
                else:
                    break
            first = point

        if equiv_group_pos == 'last' or equiv_group_pos == 'first&last':
            point = orig_point
            while point < len(sorted_items):
                if item_to_insert == sorted_items[point]:
                    point += 1
                    continue
                item1, item2 = equiv_item, sorted_items[point]
                try:
                    relation = \
                        cls._transitivity_search(item1, item2,
                                                automation=False)
                except ProofFailure:
                    msg = ("Unknown %s relationship between %s and %s"
                           % (cls, item1, item2))
                    raise TransitivityException(None, defaults.assumptions, msg)
                if isinstance(relation.expr, equiv_class):
                    equiv_item = sorted_items[point]
                    point += 1
                else:
                    break
            last = point

        if equiv_group_pos == 'first&last':
            return (first, last)
        return point

    @classmethod
    @prover
    def _transitivity_search(cls, left_item, right_item,
                             **defaults_config):
        '''
        Performs a breadth-first, bidirectional (meet in the middle) search attempting
        to prove a relation between left_item and right_item according to the RelationClass
        by applying transitivity derivations.
        If successful, the approprate Judgment relating these items (in weak or strong
        form as can be determined) is returned; otherwise a TransitivityException is raised.
        '''
        equiv_class = cls.EquivalenceClass()

        #  Check if the relation is already known directly:
        if left_item == right_item:
            # Items are the exact same, so they are equal.
            return equiv_class(left_item, right_item).prove()
        try:
            # Try the strong relation first.
            StrongClass = cls._checkedStrongRelationClass()
            relation = StrongClass(left_item, right_item)
            return relation.prove(automation=False)
        except (ProofFailure, NotImplementedError):
            # Try equality.
            try:
                # Maybe the equality is known.
                relation = equiv_class(left_item, right_item)
                return relation.prove(automation=False)
            except ProofFailure:
                pass
            # Try the weak relation if cls is weak.
            if cls == cls._checkedWeakRelationClass():
                try:
                    # Maybe the weak relation is known.
                    WeakClass = cls._checkedWeakRelationClass()
                    relation = WeakClass(left_item, right_item)
                    return relation.prove(automation=False)
                except (ProofFailure, NotImplementedError):
                    pass

        if not defaults.automation:
            relation = cls(left_item, right_item)
            msg = ('No proof found via applying transitivity amongst'
                   ' known proven relations.')
            raise TransitivityException(relation, defaults.assumptions, msg)

        sorter = TransitivitySorter(cls, [left_item, right_item],
                                    assumptions=defaults.assumptions,
                                    skip_exact_reps=False,
                                    skip_equiv_reps=False,
                                    presorted_pair=True)
        list(sorter)  # should prove desired relation
        # Return the proven relation.
        return cls._transitivity_search(left_item, right_item,
                                        automation=False)

    @classmethod
    @prover
    def _fixed_transitivity_sort(cls, items, **defaults_config):
        '''
        Check that the given items are in sorted order, returning the
        proven total ordering (conjunction of relations presented in a 
        total ordering style) if they are or raising a 
        TransitivityException if they are not.  If automation is False, 
        don't generate new relations through transitivities; assume that
        we already have the necessary direct relationships proven.
        '''
        from proveit import ExprTuple
        if isinstance(items, ExprTuple):
            items_list = items.entries
        else:
            # in case the items are a non-indexable iterable
            items_list = list(items)
        relations = []
        for item1, item2 in zip(items_list[:-1], items_list[1:]):
            relations.append(cls._transitivity_search(item1, item2))
        return total_ordering(*relations, prove=True)


class TransitivityException(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)


def total_ordering(*relations, prove=False):
    '''
    Return a conjunction of relations in the total ordering style.
    For example, "a > b >= c = d > e" is a total ordering style for
    "(a > b) and (b >= c) and (c = d) and (d > e)".  If there is a
    single relation, just return the relation.  If 'prove' is True,
    return a proven Judgment.
    '''
    from proveit import ExprRange
    from proveit.logic import And
    if len(relations) == 1 and not isinstance(relations[0], ExprRange):
        # Return a trivial, singular relation.
        relation = relations[0]
        if prove: relation = relation.prove()
        return relation
    # Return a conjunction with the proper style.
    conjunction = And(*relations)
    conjunction = conjunction.with_total_ordering_style()
    if prove:
        # Prove via composition.
        # Allow automation to prove the length requirement.
        return conjunction.conclude_via_composition(automation=True)
    return conjunction
