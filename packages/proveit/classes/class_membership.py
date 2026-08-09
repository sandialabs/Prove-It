from proveit import (Expression, Judgment, Literal, Operation,
                     defaults, USE_DEFAULTS, maybe_fenced,
                     prover, equality_prover, relation_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit.util import OrderedSet

class ClassMembership(Operation):
    '''
    A ClassMembership is an operation whose operator is a predicate that
    defines class collections.  The first operand is the object whose 
    class membership is in question.  All other operands identify the 
    particular class of interest.  Sets are special classes for which 
    membership is predicated by a relation between a member and the
    set (in fact, all relations are class memberships).
    Proper classes are non-set collections defined by predicates
    that are not member/collection relations.  A proper class, unlike a
    set, has no corresponding mathematical object to represent the
    collection itself; it only has a predicate to determine what is in the
    collection.  Sets are proven to exist by ZF axioms.  Proper classes
    only require predicate definitions.
    '''

    # maps members to their known ClassMembership Judgments.
    known_memberships = dict()
    # maps domain types and members to their known ClassMembership
    # Judgements.
    # A domain type is specified as an operator of a domain Operation.
    known_predicate_specific_memberships =  dict()
    # maps canonical forms of elements to ClassMembership Judgments.
    # For example, map x to (1*x in S) if (1*x in S) is a Judgment.
    known_memberships_by_canonical_form = dict()
    known_predicate_specific_memberships_by_canonical_form =  dict()

    def __init__(self, operator, element, *class_specifiers,
                 styles=None):
        '''
        Create a class membership operation which evaluates to True
        iff the 'element' is a member of the class defined by the operator
        predicate and the class_specifiers.
        '''
        Operation.__init__(self, operator, [element, *class_specifiers],
                           styles=styles)
        self.element = self.operands[0]
        self.predicate = operator

    @staticmethod
    def _clear_():
        CM = ClassMembership
        CM.known_memberships.clear()
        CM.known_predicate_specific_memberships.clear()
        CM.known_memberships_by_canonical_form.clear()
        CM.known_predicate_specific_memberships_by_canonical_form.clear()

    def formatted(self, format_type, **kwargs):
        '''
        Returns a formatted version of the expression for the given format_type
        ('string' or 'latex').  In the keyword arguments, fence=True indicates
        that parenthesis around the sub-expression may be necessary to avoid
        ambiguity.
        '''
        formatted_element = self.element.formatted(format_type, fence=True)
        formatted_class = self.formatted_class(format_type)
        if format_type == 'string':
            formatted = formatted_element + ' : ' + formatted_class
        if format_type == 'latex':
            formatted = formatted_element + '~:~' + formatted_class
        return maybe_fenced(format_type, formatted, **kwargs)

    def string(self, **kwargs):
        '''
        Return a string representation of the ClassMembership.
        '''
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        '''
        Return a latex-formatted representation of the ClassMembership.
        '''
        return self.formatted('latex', **kwargs)

    def formatted_class(self, format_type):
        raise NotImplementedError("'formatted_class' not implemented for %s"
                                  %type(self))

    def _record_as_proven(self, judgment):
        '''
        Store the proven membership in known_memberships,
        store the membership with the element in its canonical form
        in known_canonical_memberships, and also store in type-specific
        known memberships and canonical memberships using a descriptor
        of the operator and other operands.
        For example, IsFunction(f, A, B) would have the type descriptor
        (IsFunction.__operator__, A, B).
        '''
        Operation._record_as_proven(self, judgment)
        member = self.element
        canonical_member = member.canonical_form()
        ClassMembership.known_memberships.setdefault(
                member, OrderedSet()).add(judgment)
        ClassMembership.known_memberships_by_canonical_form.setdefault(
                canonical_member, OrderedSet()).add(judgment)
        predicate = self.predicate
        ClassMembership.known_predicate_specific_memberships.setdefault(
            (predicate, member), OrderedSet()).add(judgment)
        ClassMembership.known_predicate_specific_memberships_by_canonical_form.setdefault(
            (predicate, canonical_member), OrderedSet()).add(judgment)

    def _readily_provable(self, check_directly_known_elem_equality=True):
        '''
        Use 'as_defined' to see if it is readily provable 
        by definition.
        
        If check_directly_known_elem_equality is True and all else 
        fails, we will check the first expression directly known to
        be equal to the element to see if its membership in the daomin
        is readily provable.  This helps, for example, when there is
        an obvious definition to use.  Don't apply this recursively,
        however.
        '''
        from proveit.logic import Equals, is_irreducible_value
        element = self.element

        # If 'as_defined' is implement, check to see if that form
        # is readily provable.
        try:
            return self.as_defined().readily_provable()
        except NotImplementedError:
            pass

        # check if this is readily provable from the element side
        if hasattr(element, 'readily_provable_membership_inclusion'):
            if element.readily_provable_membership_inclusion(self):
                return True

        # Try a known evaluation.
        if not is_irreducible_value(element):
            try:
                elem_eval = Equals.get_known_evaluation(element).rhs
            except UnsatisfiedPrerequisites:
                return None
            try:
                return type(self)(elem_eval, 
                                  *self.operands[1:]).readily_provable()
            except:
                return False

        if check_directly_known_elem_equality:
            # Check the first directly known equality of the element to
            # see if this equal expression's membership is readily 
            # provable.
            from proveit.logic import InSet, NotInSet
            for eq_expr in Equals.yield_directly_known_eq_exprs(
                    element, include_canonical_forms=False):
                try:
                    kwargs = dict()
                    if isinstance(self, InSet) or isinstance(self, NotInSet):
                        kwargs['check_directly_known_elem_equality']=False
                    if type(self)(eq_expr, *self.operands[1:]).readily_provable(
                            **kwargs):
                        return True
                except:
                    pass
                return False

        return False

    def _readily_disprovable(self):
        '''
        By default, we will determine if this membership is
        readily disprovable if its "as_defined()" expression is
        readily disprovable.
        '''
        try:
            return self.as_defined().readily_disprovable()
        except NotImplementedError:
            # If 'as_defined' is not implemented, this default
            # method for determining provability can never be true.
            return False

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude this class membership predicate.
        '''
        from proveit.logic import (Equals, is_irreducible_value,
                                   InSet, NotInSet)

        element = self.element

        try:
            if self.as_defined().readily_provable():
                # Proof by definition.
                definition = self.definition()
                return definition.derive_left_via_equality()
        except NotImplementedError:
            # The 'as_defined' is not implemented.
            pass

        # check if this is readily provable from the element side;
        # if so, call 'deduce_belonging' on the element.
        if hasattr(element, 'readily_provable_membership_inclusion'):
            if element.readily_provable_membership_inclusion(self):
                return element.deduce_membership_inclusion(self)

        # Try a known evaluation of the element.
        if not is_irreducible_value(element):
            try:
                evaluation = Equals.get_known_evaluation(element)
            except UnsatisfiedPrerequisites:
                evaluation = None
            if evaluation is not None:
                membership = type(self)(evaluation.rhs, *self.operands[1:])
                if membership.readily_provable():
                    membership = membership.prove()
                    return membership.inner_expr().element.substitute(
                            element)
        
        # Check the first directly known expression equal to the element
        # to see if we can prove it's membership.
        for eq_expr in Equals.yield_directly_known_eq_exprs(
                element, include_canonical_forms=False):
            membership_of_eq_expr = type(self)(eq_expr, *self.operands[1:])
            # Avoid applying this check recursively.
            kwargs = dict()
            if isinstance(self, InSet) or isinstance(self, NotInSet):
                kwargs['check_directly_known_elem_equality']=False
            if membership_of_eq_expr.readily_provable(**kwargs):
                membership_of_eq_expr = membership_of_eq_expr.prove()
                return membership_of_eq_expr.inner_expr().element.substitute(
                        element)
            break # only try the first known equal expression
        
        raise ProofFailure(self, defaults.assumptions,
                           "Unable to conclude automatically.")

    @staticmethod
    def _yield_known_memberships(element, *, predicate=None,
                                 include_canonical_forms=True,
                                 assumptions=USE_DEFAULTS):
        '''
        Yield the known memberships of the given element applicable
        under the given assumptions.  If provided with a predicate, restrict
        to classes defined by that predicate.
        If 'include_canonical_forms' is
        True, then we can treat elements of the same canonical form
        as the same for this purpose.
        '''
        from proveit._core_.proof import Assumption
        known_memberships = (
                ClassMembership.known_memberships_by_canonical_form if 
                include_canonical_forms else ClassMembership.known_memberships)
        with defaults.temporary() as tmp_defaults:
            if assumptions is not USE_DEFAULTS:
                tmp_defaults.assumptions = assumptions
            # Make sure we derive assumption side-effects first.
            Assumption.make_assumptions()

            if include_canonical_forms:
                key = element.canonical_form()
                known_memberships = (
                    ClassMembership.known_memberships_by_canonical_form)
                known_predicate_specific_memberships = (
                    ClassMembership.
                    known_predicate_specific_memberships_by_canonical_form)
            else:
                key = element
                known_memberships = ClassMembership.known_memberships
                known_predicate_specific_memberships = (
                    ClassMembership.known_predicate_specific_memberships)
            if predicate is not None:
                key = (predicate, key)
                known_memberships = known_predicate_specific_memberships

            if key in known_memberships:
                for known_membership in known_memberships[key]:
                    if known_membership.is_applicable():
                        yield known_membership

    @classmethod
    def yield_known_memberships(cls, element, *, predicate=None,
                                include_canonical_forms=True,
                                assumptions=USE_DEFAULTS):
        '''
        Yield the known memberships of the given element applicable
        under the given assumptions.  If the class has an _operator_ method,
        use that as the default predicate.  Restrict to classes defined by
        the predicate if applicable.
        If 'include_canonical_forms' is
        True, then we can treat elements of the same canonical form
        as the same for this purpose.
        '''
        if predicate is None and hasattr(cls, '_operator_'):
            predicate = cls._operator_
        for membership in ClassMembership._yield_known_memberships(
                element, include_canonical_forms=include_canonical_forms,
                predicate=predicate, assumptions=assumptions):
            yield membership

    @staticmethod
    def has_known_membership(element, *, predicate=None, 
                             include_canonical_forms=True,
                             assumptions=USE_DEFAULTS):
        try:
            next(predicate.yield_known_memberships(
                element, include_canonical_forms=include_canonical_forms,
                predicate=predicate, assumptions=assumptions))
            return True
        except StopIteration:
            return False # no known memberships

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Simplify this ClassMembership according to its
        'definition' method if there is one.
        '''
        from proveit.logic import Equals, TRUE, FALSE, EvaluationError

        try:
            definition = self.definition()
        except NotImplementedError:
            definition = None
        if definition is None or (definition.lhs == definition.rhs):
            # definition failed or is trivial
            return Operation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        try:
            rhs_eval = definition.rhs.evaluation(automation=must_evaluate)
        except EvaluationError as e:
            if must_evaluate:
                raise e
            return Operation.shallow_simplification(self)
        evaluation = definition.apply_transitivity(rhs_eval)
        
        # Try also to evaluate this by deducing membership
        # or non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                self.prove()
            else:
                self.disprove()
        except BaseException:
            pass
        return evaluation

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove and return the membership equal to an expression that
        defines the membership.
        '''
        raise NotImplementedError(
            "%s, has no 'definition' method implemented" % str(
                self.__class__))

    def as_defined(self):
        '''
        Returns the expression that defines the membership.
        '''
        raise NotImplementedError(
            "%s, has no 'as_defined' method implemented" % str(
                self.__class__))

    @equality_prover('canonical_equated', 'canonical_equate')
    def _deduce_canonically_equal(self, rhs, **defaults_config):
        '''
        Equate 'self' to the 'rhs' via the definition if 'definition' is
        implemented.
        '''
        try:
            definition = self.definition()
        except NotImplementedError:
            return Operation._deduce_canonically_equal(self, rhs)
        def_eq_rhs = definition.deduce_canonically_equal(rhs)
        return definition.apply_transitivity(def_eq_rhs)

    @staticmethod
    def check_proven_class_membership(membership, member, predicate):
        '''
        Raise a ValueError unless membership is a proven Judgment for a
        ClassMembership with the given predicate and member.
        '''
        if (not isinstance(membership, Judgment)
                or not isinstance(membership.expr, ClassMembership)
                or membership.predicate != predicate
                or membership.element != member):
            raise ValueError(
                    "Failed to meet expectation: %s is supposed to be a "
                    "proven Judgment that %s is a member of a class "
                    "defined by the predicate %s"
                    %(membership, member, predicate))
