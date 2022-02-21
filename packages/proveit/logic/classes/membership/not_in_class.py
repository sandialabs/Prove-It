from proveit import (Literal, defaults, USE_DEFAULTS,
                     prover, relation_prover, equality_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit.relation import Relation
from proveit import x, S


class NotInClass(Relation):
    '''
    NotInClass denotes the logical negation of class membership
    (see InClass).
    '''
    
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in_{C}',
                         latex_format=r'\notin_{C}',
                         theory=__file__)

    # maps elements to NotInSet Judgments.
    # For example, map x to (x \nin S) if (x \nin S) is a Judgment.
    known_nonmemberships = dict()

    # map (element, domain) pairs to corresponding NotInClass expressions
    notinclass_expressions = dict()

    def __init__(self, element, domain, *, 
                 operator=None, styles=None):
        '''
        Create an class nonmembership relation indicating that the
        given 'element' is NOT in the given 'domain'.  If an 'operator'
        is provide, use this as the operator instead of
        NotInClass._operator_ (e.g., for NotInSet which derives from
        NotInClass but uses a distinct operator).
        '''
        if operator is None:
            operator = NotInClass._operator_        
        Relation.__init__(self, operator, element, domain,
                          styles=styles)
        self.element = self.operands[0]
        self.domain = self.operands[1]
        NotInClass.notinclass_expressions[(self.element, self.domain)] = self
        if hasattr(self.domain, 'nonmembership_object'):
            self.nonmembership_object = self.domain.nonmembership_object(
                element)
            if not isinstance(self.nonmembership_object, ClassNonmembership):
                raise TypeError(
                    "The 'nonmembership_object' of %s is a %s which "
                    "is not derived from %s as it should be." %
                    (self.domain, self.nonmembership_object.__class__,
                        ClassNonmembership))

    def __dir__(self):
        '''
        If the domain has a 'nonmembership_object' method,
        include methods from the object it generates (also
        'unfold' which defaults as 'unfold_not_in' if it isn't
        defined in 'nonmembership_object').
        '''
        if 'nonmembership_object' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) +
                              dir(self.membership_object)))
        else:
            return sorted(list(self.__dict__.keys()) + 'unfold')

    def __getattr__(self, attr):
        '''
        If the domain has a 'nonmembership_object' method,
        include methods from the object it generates (also
        'unfold' defaults as 'unfold_not_in' if it isn't
        defined in 'nonmembership_object').
        '''
        if attr in ('lhs', 'rhs'):
            return Relation.__getattr__(self, attr)
        if 'nonmembership_object' in self.__dict__:
            return getattr(self.nonmembership_object, attr)
        elif attr == 'unfold':
            return self.unfold_not_in  # the default 'unfold' method
        raise AttributeError

    def side_effects(self, judgment):
        '''
        Store the proven non-membership in known_nonmemberships.
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembership_object' method, side effects
        will also be generated from the 'side_effects' object that it
        generates.
        '''
        NotInClass.known_nonmemberships.setdefault(
            self.element, set()).add(judgment)
        yield self.unfold_not_in
        if hasattr(self, 'nonmembership_object'):
            for side_effect in self.nonmembership_object.side_effects(
                    judgment):
                yield side_effect

    def negated(self):
        '''
        Return the membership expression (double negative),
        element in domain.
        '''
        from .in_class import InClass
        return InClass(self.element, self.domain)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this 'not in' statement is in the set
        of BOOLEANS. For example,
        NotInSet(x, {1, 2, 3}).deduce_in_bool()
        returns |- NotInSet(x, {1, 2, 3}) in Bool
        '''
        from . import not_in_class_is_bool
        return not_in_class_is_bool.instantiate(
                {x: self.element, S: self.domain})

    @prover
    def unfold_not_in(self, **defaults_config):
        r'''
        From (x \notin y), derive and return Not(x \in y).
        '''
        from . import unfold_not_in_class
        # We include the auto_simplify=False to keep the membership
        # result inside the Not() from being reduced to False.
        return unfold_not_in_class.instantiate(
            {x: self.element, S: self.domain}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the the NotInSet object is true ---
        i.e. that the element is not in the domain.
        First, see if it is not contained in a superset of the domain.
        Next, check if the element has a known simplification; if so,
        try to derive non-membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.nonmembership_object.conclude(..)' method to
        prove the non-membership.  If that fails, try simplifying the
        element again, this time using automation to push the
        simplification through if possible.
        As a last resort, try 'conclude_as_folded'.
        '''
        from proveit import ProofFailure
        from proveit.logic import SubsetEq, SimplificationError
        
        if self.negated().disproven():
            return self.conclude_as_folded()

        # See if the element, or something known to be equal to
        # the element, is known to be a nonmember of the domain or a 
        # superset of the domain.
        if self.element in NotInClass.known_nonmemberships:
            for known_nonmembership in \
                    NotInClass.known_nonmemberships[self.element]:
                if known_nonmembership.is_applicable():
                    # x not in R is known to be true; if we know that
                    # S subset_eq R, we are done.
                    rel = SubsetEq(self.domain,
                                   known_nonmembership.domain)
                    if rel.proven():
                        # S is a subset of R, so now we can prove 
                        # x not in S.
                        return rel.derive_subset_nonmembership(
                            self.element)
        # No known nonmembership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(automation=True)
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None  # reflection doesn't count
        except (SimplificationError, ProofFailure,
                UnsatisfiedPrerequisites, NotImplementedError):
            elem_simplification = None

        # If the element simplification succeeded, prove the
        # nonmembership via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_nonmembership = self.__class__(
                simple_elem, self.domain).prove(preserve_all=True)
            inner_expr = simple_nonmembership.inner_expr().element
            return elem_simplification.sub_left_side_into(inner_expr)
        else:
            # If it has a 'nonmembership_object', try to conclude
            # nonmembership using that.
            if hasattr(self, 'nonmembership_object'):
                return self.nonmembership_object.conclude()
            else:
                # Otherwise, attempt to conclude via Not(x in S)
                return self.conclude_as_folded()

        raise ProofFailure(self, defaults.assumptions,
                "%s.conclude() has failed to find a proof for the "
                "non-membership: %s"%(self.__class__, self))

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Attempt to conclude x not in C via Not(x in C).
        '''
        from . import fold_not_in_class
        return fold_not_in_class.instantiate(
            {x: self.element, S: self.domain})

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Attempt to evaluate whether some x ∉ S is TRUE or FALSE
        using the 'definition' method of the domain's 
        'nonmembership_object' if there is one.
        '''
        from proveit.logic import TRUE, EvaluationError

        if not must_evaluate:
            # Don't oversimplify!
            # Unless 'must_evaluate' is true, we'll forgo the
            # treatment below.
            return Relation.shallow_simplification(
                    self, must_evaluate=must_evaluate)

        # try an 'definition' method (via the nonmembership object)
        if not hasattr(self, 'nonmembership_object'):
            # Don't know what to do otherwise.
            return Relation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        definition = self.nonmembership_object.definition()
        try:
            rhs_eval = definition.rhs.evaluation(automation=must_evaluate)
        except EvaluationError as e:
            if must_evaluate:
                raise e
            return Relation.shallow_simplification(self)
        evaluation = definition.apply_transitivity(rhs_eval)

        # try also to evaluate this by deducing membership or 
        # non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'nonmembership_object'):
                    self.nonmembership_object.conclude()
            else:
                in_domain = self.negated()
                if hasattr(in_domain, 'nonmembership_object'):
                    in_domain.nonmembership_object.conclude()
        except BaseException:
            pass
        return evaluation

class ClassNonmembership:
    '''
    Base class for any 'nonmembership object' return by a domain's
    'nonmembership_object' method.
    '''

    def __init__(self, element, domain, *, expr=None):
        self.element = element
        self.domain = domain
        # The expression represented by this NonMembership.
        if expr is not None:
            self.expr = expr
        elif (self.element, self.domain) in NotInClass.notinclass_expressions:
            self.expr = NotInClass.notinclass_expressions[(self.element, 
                                                       self.domain)]
        else:
            self.expr = NotInClass(self.element, self.domain)

    def side_effects(self, judgment):
        raise NotImplementedError(
            "Nonmembership object has no 'side_effects' method implemented")

    def conclude(self, assumptions):
        raise NotImplementedError(
            "Nonmembership object has no 'conclude' method implemented")

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'definition' method implemented")

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError(
            "Nonmembership object has no 'deduce_in_bool' method implemented")
