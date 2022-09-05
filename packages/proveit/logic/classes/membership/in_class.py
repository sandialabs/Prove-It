from proveit import (Expression, Judgment, Literal, defaults, USE_DEFAULTS,
                     prover, equality_prover, relation_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit.relation import Relation
from proveit.util import OrderedSet

class InClass(Relation):
    '''
    Class membership denotes a collection of mathmematical objects
    that satisfy a certain common property.  It is distinct from set
    membership, however.  In particular, subsets of sets may be defined
    via subset comprehension, but there is no such analogue for classes.
    In this manner, classes can be more inclusive than sets without 
    worrying about Russel's paradox.  A class that is not a set is 
    called a proper class.  
    
    Note: Expressions objects that represent proper classes should have
    an attribute called 'is_proper_class' that is True.  This will
    ensure that when such an object is used as a domain, it will
    automatically make an InClass condition instead of InSet.
    '''

    # operator of the InClass operation.
    # The formatting is the same as InSet, but the operation is
    # distinct.
    _operator_ = Literal(
            string_format='in_c', 
            latex_format=r'\underset{{\scriptscriptstyle c}}{\in}',
            theory=__file__)

    # maps elements to their known InClass Judgments.
    known_memberships = dict()
    # maps canonical forms of elements to InClass Judgments.
    # For example, map x to (1*x in S) if (1*x in S) is a Judgment.
    known_memberships_by_canonical_form = dict()
    
    # map (element, domain) pairs to corresponding InClass expressions
    inclass_expressions = dict()

    def __init__(self, element, domain, *, 
                 operator=None, styles=None):
        '''
        Create a class membership relation indicating that the
        given 'element' is in the given 'domain'.  If an 'operator'
        is provide, use this as the operator instead of
        InClass._operator_ (e.g., for InSet which derives from
        InClass but uses a distinct operator).
        '''
        if operator is None:
            operator = InClass._operator_
        Relation.__init__(self, operator, element, domain,
                          styles=styles)
        self.element = self.operands[0]
        self.domain = self.operands[1]
        InClass.inclass_expressions[(self.element, self.domain)] = self
        if hasattr(self.domain, 'membership_object'):
            self.membership_object = self.domain.membership_object(element)
            if not isinstance(self.membership_object, ClassMembership):
                raise TypeError(
                    "The 'membership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.membership_object.__class__, 
                     ClassMembership))

    def __dir__(self):
        '''
        If the domain has a 'membership_object' method, include
        methods from the object it generates.
        '''
        if 'membership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(self.__dict__.keys())

    def __getattr__(self, attr):
        '''
        If the domain has a 'membership_object' method, include
        methods from the object it generates.
        '''
        if attr in ('lhs', 'rhs'):
            return Relation.__getattr__(self, attr)
        if 'membership_object' in self.__dict__:
            return getattr(self.membership_object, attr)
        raise AttributeError

    @staticmethod
    def reversed_operator_str(formatType):
        '''
        Reversing \in gives \ni.  Reversing "in" gives "contains".
        '''
        if formatType=='latex':
            return '\ni_{C}'
        else:
            return 'contains_C'

    def _record_as_proven(self, judgment):
        '''
        Store the proven membership in known_memberships, and
        store the membership with the element in its canonical form
        in known_canonical_memberships.
        '''
        Relation._record_as_proven(self, judgment)
        InClass.known_memberships.setdefault(
                self.element, OrderedSet()).add(judgment)
        InClass.known_memberships_by_canonical_form.setdefault(
                self.element.canonical_form(), OrderedSet()).add(judgment)
        
    def side_effects(self, judgment):
        '''
        If the domain has a 'membership_object' method, side effects
        will also be generated from the 'side_effects' object that it
        generates.
        '''
        if hasattr(self, 'membership_object'):
            for side_effect in self.membership_object.side_effects(judgment):
                yield side_effect

    def negation_side_effects(self, judgment):
        '''
        Fold Not(x in S) as (x not-in S) as an automatic side-effect.
        '''
        yield self.deduce_not_in

    def negated(self):
        '''
        Return the negated membership expression,
        element not in domain.
        '''
        from .not_in_class import NotInClass
        return NotInClass(self.element, self.domain)

    @prover
    def deduce_not_in(self, **defaults_config):
        r'''
        Deduce x not in C assuming not(A in C), where self = (x in C).
        '''
        return self.negated().prove()

    def _build_canonical_form(self):
        '''
        The canonical form of this membership is based upon
        'as_defined' which defines what the membership means.
        '''
        if hasattr(self, 'membership_object'):
            return self.membership_object._build_canonical_form()
        else:
            return Relation._build_canonical_form(self)

    def _readily_provable(self, check_directly_known_elem_equality=True):
        '''
        This membership is readily provable if the membership
        object indicates that it is readily provable.
        
        If check_directly_known_elem_equality is True and all else 
        fails, we will check the first expression directly known to
        be equal to the element to see if its membership in the daomin
        is readily provable.  This helps, for example, when there is
        an obvious definition to use.  Don't apply this recursively,
        however.
        '''
        from proveit.logic import Equals, is_irreducible_value
        if hasattr(self, 'membership_object'):
            if self.membership_object._readily_provable():
                return True
        element = self.element
        domain = self.domain
        
        # Try a known evaluation.
        if not is_irreducible_value(element):
            try:
                elem_eval = Equals.get_known_evaluation(element).rhs
            except UnsatisfiedPrerequisites:
                return None
            return type(self)(elem_eval, self.domain).readily_provable()

        if check_directly_known_elem_equality:
            # Check the first directly known equality of the element to
            # see if this equal expression's membership is readily 
            # provable.
            for eq_expr in Equals.yield_directly_known_eq_exprs(
                    element, include_canonical_forms=False):
                if type(self)(eq_expr, domain).readily_provable(
                        check_directly_known_elem_equality=False):
                    return True
                return False
            
        return False

    def _readily_disprovable(self):
        '''
        This membership is readily disprovable if the corresponding
        nonmembership is readily provable.
        '''
        return self.negated().readily_provable()

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the element is in the domain.  Try
        standard relation strategies (evaluate or somplify both sides).
        If that doesn't work, try using the domain-specific 'conclude' 
        method of the membership object.
        '''
        from proveit.logic import Equals, is_irreducible_value
        
        if hasattr(self, 'membership_object') and (
                self.membership_object._readily_provable()):
            # Don't bother with a fancy, indirect approach if
            # we can readily conclude membership via the membership
            # object.
            return self.membership_object.conclude()

        # Try a known evaluation of the element.
        element = self.element
        domain = self.domain
        if not is_irreducible_value(element):
            try:
                evaluation = Equals.get_known_evaluation(element)
            except UnsatisfiedPrerequisites:
                evaluation = None
            if evaluation is not None:
                membership = type(self)(evaluation.rhs, domain)
                if membership.readily_provable():
                    membership = membership.prove()
                    return membership.inner_expr().element.substitute(
                            element)
        
        # Check the first directly known expression equal to the element
        # to see if we can prove it's membership.
        for eq_expr in Equals.yield_directly_known_eq_exprs(
                element, include_canonical_forms=False):
            membership_of_eq_expr = type(self)(eq_expr, domain)
            # Avoid applying this check recursively.
            if membership_of_eq_expr.readily_provable(
                    check_directly_known_elem_equality=False):
                membership_of_eq_expr = membership_of_eq_expr.prove()
                return membership_of_eq_expr.inner_expr().element.substitute(
                        element)
            break # only try the first known equal expression
        
        # Try the standard Relation strategies -- evaluate or
        # simplify both sides.
        try:
            return Relation.conclude(self)
        except ProofFailure:
            # Both sides are already irreducible or simplified
            # or we were unable to simplify either side.
            pass

        # Unable to simplify the element.  Try to conclude via
        # the 'membership_object' if there is one.
        if hasattr(self, 'membership_object'):
            return self.membership_object.conclude()

        raise ProofFailure(self, defaults.assumptions,
                           "Unable to conclude automatically; "
                           "the domain, %s, has no 'membership_object' "
                           "method with a strategy for proving "
                           "membership." % self.domain)

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude that the element is not in the domain
        via proving nonmembership.
        '''
        nonmembership = self.negated()
        return nonmembership.prove().unfold_not_in()

    @staticmethod
    def yield_known_memberships(element, *, include_canonical_forms=True,
                                 assumptions=USE_DEFAULTS):
        '''
        Yield the known memberships of the given element applicable
        under the given assumptions.  In 'include_canonical_forms' is
        True, then we can treat elements of the same canonical form
        as the same for this purpose.
        '''
        from proveit._core_.proof import Assumption
        known_memberships = (
                InClass.known_memberships_by_canonical_form if 
                include_canonical_forms else InClass.known_memberships)
        with defaults.temporary() as tmp_defaults:
            if assumptions is not USE_DEFAULTS:
                tmp_defaults.assumptions = assumptions
            # Make sure we derive assumption side-effects first.
            Assumption.make_assumptions()
    
            if include_canonical_forms: 
                key = element.canonical_form()
            else:
                key = element
            if key in known_memberships:
                for known_membership in known_memberships[key]:
                    if known_membership.is_applicable():
                        yield known_membership

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Attempt to evaluate whether some x ∊ S is TRUE or FALSE
        using the 'definition' method of the domain's 
        'membership_object' if there is one.
        '''
        from proveit.logic import TRUE, EvaluationError
        
        if not must_evaluate:
            # Don't oversimplify!
            # Unless 'must_evaluate' is true, we'll forgo the
            # treatment below.
            return Relation.shallow_simplification(
                    self, must_evaluate=must_evaluate)

        # try a 'definition' method (via the membership object)
        if not hasattr(self, 'membership_object'):
            # Don't know what to do otherwise.
            return Relation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        try:
            definition = self.membership_object.definition()
        except NotImplementedError:
            # Don't know what to do otherwise.
            return Relation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        try:
            rhs_eval = definition.rhs.evaluation(automation=must_evaluate)
        except EvaluationError as e:
            if must_evaluate:
                raise e
            return Relation.shallow_simplification(self)
        evaluation = definition.apply_transitivity(rhs_eval)
        
        # Try also to evaluate this by deducing membership
        # or non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                self.membership_object.conclude()
            else:
                not_in_domain = self.negated()
                if hasattr(not_in_domain, 'nonmembership_object'):
                    not_in_domain.nonmembership_object.conclude()
        except BaseException:
            pass
        return evaluation
    
    @staticmethod
    def check_proven_class_membership(membership, element, class_of_class):
        if (not isinstance(membership, Judgment)
                or not isinstance(membership.expr, InClass)
                or membership.element != element
                or not isinstance(membership.domain, class_of_class)):
            raise ValueError(
                    "Failed to meet expectation: %s is supposed to be a "
                    "proven Judgment that %s is a member of a class "
                    "represented by an Expression of type %s"
                    %(membership, element, class_of_class))        


class ClassMembership:
    def __init__(self, element, domain, *, expr=None):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        self.element = element
        self.domain = domain
        # The expression represented by this Membership.
        if expr is not None:
            self.expr = expr
        if (self.element, self.domain) in InClass.inclass_expressions:
            self.expr = InClass.inclass_expressions[(self.element, self.domain)]
        else:
            self.expr = InClass(self.element, self.domain)

    def side_effects(self, judgment):
        raise NotImplementedError(
            "Membership object, %s, has no 'side_effects' method implemented" % str(
                self.__class__))

    def _build_canonical_form(self):
        '''
        The canonical form of this membership is based upon
        'as_defined' which defines what the membership means.
        '''
        try:
            return self.as_defined().canonical_form()
        except NotImplementedError:
            # If 'as_defined' is not implemented, use the default
            # method of building the canonical form.
            return Relation._build_canonical_form(self.expr)

    def _readily_provable(self):
        '''
        By default, we will determine if this membership is
        readily provable if its "as_defined()" expression is
        readily provable.
        '''
        try:
            return self.as_defined().readily_provable()
        except NotImplementedError:
            # If 'as_defined' is not implemented, this default
            # method for determining provability can never be true.
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
        raise NotImplementedError(
            "Membership object, %s, has no 'conclude' method implemented" % str(
                self.__class__))

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove the membership equal to an expression that defines the
        membership.
        '''
        raise NotImplementedError(
            "Membership object, %s, has no 'definition' method implemented" % str(
                self.__class__))
    
    def as_defined(self):
        '''
        Returns the expression that defines the membership.
        '''
        raise NotImplementedError(
            "Membership object, %s, has no 'as_defined' method implemented" % str(
                self.__class__))

    def readily_in_bool(self, **defaults_config):
        '''
        Unless this is overridden, we won't presume that the membership
        is readily provable to be boolean.
        '''
        return False

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        raise NotImplementedError(
            "Membership object, %s, has no 'deduce_in_bool' method implemented" % str(
                self.__class__))

