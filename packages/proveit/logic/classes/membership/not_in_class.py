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

    def _record_as_proven(self, judgment):
        '''
        Store the proven non-membership in known_nonmemberships.
        '''
        Relation._record_as_proven(self, judgment)
        NotInClass.known_nonmemberships.setdefault(
            self.element, set()).add(judgment)
        
    def side_effects(self, judgment):
        '''
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembership_object' method, side effects
        will also be generated from the 'side_effects' object that it
        generates.
        '''
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

    def _build_canonical_form(self):
        '''
        The canonical form of this membership is based upon
        'as_defined' which defines what the membership means.
        '''
        if hasattr(self, 'nonmembership_object'):
            return self.nonmembership_object._build_canonical_form()
        else:
            return Relation._build_canonical_form(self)

    def _readily_provable(self):
        '''
        This nonmembership is readily provable if the membership
        has been disproven, the nonmembership object indicates that it 
        is readily provable or if there is a known stronger 
        nonmembership.
        '''
        if self.negated().disproven():
            # Use disproven instead of readily disproven to avoid 
            # infinite recursion.
            return True
        if hasattr(self, 'nonmembership_object'):
            if self.nonmembership_object._readily_provable():
                return True
        return False

    def _readily_disprovable(self):
        '''
        This nonmembership is readily disprovable if the corresponding
        membership is readily provable.
        '''
        return self.negated().readily_provable()

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the the NotInSet object is true ---
        i.e. that the element is not in the domain.
        First see if the corresponding membership has been disproven. 
        Then try the ses the Relation conclude strategies that simplify 
        both sides.  Finally use the domain-specific conclude method of 
        the nonmembership object as a last resort.
        '''        
        if self.negated().disproven(): # don't use readily_disprovable
            return self.conclude_as_folded()

        # Try the standard Relation strategies -- evaluate or
        # simplify both sides.
        try:
            return Relation.conclude(self)
        except ProofFailure:
            # Both sides are already irreducible or simplified
            # or we were unable to simplify either side.
            pass

        # If it has a 'nonmembership_object', try to conclude
        # nonmembership using that.
        if hasattr(self, 'nonmembership_object'):
            return self.nonmembership_object.conclude()
        else:
            # Otherwise, attempt to conclude via Not(x in S)
            return self.conclude_as_folded()

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude the negation of nonmembership via
        proving membership.
        '''
        from . import double_negated_membership
        return double_negated_membership.instantiate(
                {x:self.element, S:self.domain})

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Attempt to conclude x not in C via Not(x in C).
        '''
        from . import fold_not_in_class
        return fold_not_in_class.instantiate(
            {x: self.element, S: self.domain})

    @staticmethod
    def yield_known_nonmemberships(element, assumptions=USE_DEFAULTS):
        '''
        Yield the known nonmemberships of the given element applicable
        under the given assumptions.
        '''
        from proveit._core_.proof import Assumption
        # Make sure we derive assumption side-effects first.
        assumptions = defaults.checked_assumptions(assumptions)
        Assumption.make_assumptions(defaults.assumptions)

        if element in NotInClass.known_nonmemberships:
            for known_nonmembership in (
                    NotInClass.known_nonmemberships[element]):
                if known_nonmembership.is_applicable(assumptions):
                    yield known_nonmembership

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

    def _build_canonical_form(self):
        '''
        The canonical form of this nonmembership is based upon
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
        By default, we will determine if this nonmembership is
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
        By default, we will determine if this nonmembership is
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
            "Nonmembership object has no 'conclude' method implemented")

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'definition' method implemented")

    def as_defined(self):
        '''
        Returns the expression that defines the nonmembership.
        '''
        raise NotImplementedError(
            "Nonmembership object, %s, has no 'as_defined' method implemented" 
            % str(self.__class__))

    @prover
    def deduce_in_bool(self, **defaults_config):
        raise NotImplementedError(
            "Nonmembership object has no 'deduce_in_bool' method implemented")
