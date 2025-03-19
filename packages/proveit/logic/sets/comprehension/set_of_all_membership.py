from proveit import USE_DEFAULTS, equality_prover, prover, Function
from proveit.logic import And, SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import f, n, x, y, S, Q

class SetOfAllMembership(SetMembership):
    '''
    Defines methods that apply to membership in a set comprehension,
    i.e. membership in a SetOfAll construction such as x being in the
    set of all squares of positive integers:

        InSet(x, SetOfAll(i, Exp(i, two), conditions=[greater(i, zero)],
                          domain=Integer))

    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the comprehension set membership as a side-effect.
        '''
        yield self.unfold # STILL TO BE ADDRESSED

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return an equality depending on the form of the
        SetOfAll set comprehension serving as the domain.
        (1) From [x in {y | Q(y)}_{y in S}], deduce and return
            [x in {y|Q(y)}_{y in S}] = [(x in S) and Q(x)].
        (2) From [x in {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}], deduce
            and return [x in {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}] =
            [(x in S) and (Q1(y) and Q2(y),..., and Qn(y))].
        (3) From [x in {f(y) | ..Q(y)..}]_{y in S}], deduce and return
            [x in {f(y) | ..Q(y)..}]_{y in S}] =
                exists_{y in S | ..Q(y)..} [x = f(y)].
        The process for producing the outcome is very similar to the
        process used in the unfold() method defined further below.
        '''

        from . import comprehension_def, basic_comprehension

        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())

        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)

        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # simple case of [x in {y | Q(y)}_{y in S}]
            # or [x in {y | Q1(y), ..., Qn(y)}_{y in S}]:
            _S_sub = self.domain.all_domains()[0] # only 1 instance var
            _y_sub = self.domain.all_instance_vars()
            return basic_comprehension.instantiate(
                    {S:_S_sub, _Q_op:_Q_op_sub, x:element, y:_y_sub})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars
            _n_sub = num(len(self.domain.all_instance_vars()))
            _f_op, _f_op_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            _S_sub = self.domain.all_domains()
            _y_sub = self.domain.all_instance_vars()
            # if len(self.domain.explicit_conditions())<=1:
            #     should_auto_simplify = True
            #     # will simplify vacuous And() and trivial And(Q(y))
            # else:
            #     should_auto_simplify = False
            return comprehension_def.instantiate(
                {n:_n_sub, S:_S_sub, _Q_op:_Q_op_sub, _f_op:_f_op_sub,
                x:element, y:_y_sub})

    def as_defined(self):
        '''
        TBA. The idea here is to return (but do not derive) the
        'unfolded' version (i.e. the definition) of a
        SetOfAllMembership expression, depending on the form of the
        membership object:
        (1) From (x in {y | Q(y)})_{y in S}, return [(x in S) and Q(x)].
        (2) From (x in {y | ..Q(y)..})_{y in S},
            return [(x in S) and ..Q(x)..].
        (3) From (x in {f(y) | ..Q(y)..})_{y in S}, return
            exists_{y in S | ..Q(y)..} x = f(y).
        In the case of a simple Union() membership, the disjunction of
        memberships is easily constructed and you might want such a
        definition without having to instantiate the unfold theorem
        and actually derive the definition result.
        In the case of a SetOfAllMembership, the situation is more
        complicated, with the explicit conditions potentially being
        quite varied.

        # From the original UnionMembership comments:
        From self=[elem in (A U B U ...)], return
        [(element in A) or (element in B) or ...].
        '''

        # From the original UnionMembership code:
        # from proveit.logic import Or, InSet
        # element = self.element
        # return Or(*self.domain.operands.map_elements(
        #         lambda subset : InSet(element, subset)))

        raise NotImplementedError(
                "SetOfAllMembership.as_defined() not yet implemented.")

    @prover
    def unfold(self, **defaults_config):
        '''
        Return an 'unfolded' version of a SetOfAllMembership expression,
        depending on the form of the membership object:
        (1) From (x in {y | Q(y)})_{y in S}, derive and return
            [(x in S) and Q(x)].
        (2) From (x in {y | ..Q(y)..})_{y in S}, derive and return
            [(x in S) and ..Q(x)..].
        (3) From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return
            exists_{y in S | ..Q(y)..} x = f(y) (and derive x in S,
            but this is not returned).

        Examples.

        (1) Let A1 = SetOfAll(y, y, y >= 0, domain = Real). Then
            (x in A1).unfold(assumptions=[x in A1]) derives and returns
            {x in A1} |- (x in Real) AND (x >= 0)

        (2) Let A2 = SetOfAll(y, y, conditions=[y > 0, y < 11],
                     domain = Integer). Then
            (x in A2).unfold(assumptions=[x in A2]) derives and returns
            {x in A2} |- (x in Integer) AND ((x > 0) AND (x < 11))

        (3) Let A3 = SetOfAll(i, ExprTuple(i, zero),
                     domain = Interval(zero, num(10))),
            which gives a set of tuples like this:
                {(0,0), (1,0), ... (10,0)}
            Then (x in A3).unfold(assumptions=[x in A3]) derives and
            returns:
            x in A3 |- Exists_{i in {0, 1, ..., 10}} s.t. x = (i, 0).

        The method currently returns an error when the underlying
        SetOfAll set uses multiple instance variables with multiple
        explicit conditions. The reason for this is unclear but appears
        to be the result of the instantiation of the unfold theorem
        producing an antecedent that does not exactly match the
        original membership object.
        '''

        from . import (unfold, unfold_basic_comprehension,
                       in_superset_if_in_comprehension)

        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())
        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)
        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # simple case of [x in {y | Q(y)}_{y in S}]
            # or [x in {y | Q1(y), ..., Qn(y)}_{y in S}]: derive
            # (but don't) explicitly return) side-effect (x in S);
            # We do this here because some cases below do not include
            # the membership (x in S) in the returned result
            in_superset_if_in_comprehension.instantiate(
                    {S: self.domain.domain, _Q_op: _Q_op_sub,
                     x: element, y: self.domain.instance_var})
            if len(self.domain.explicit_conditions())==1:
                _Q_op, _Q_op_sub = (
                    Function(Q, self.domain.all_instance_vars()),
                    explicit_conditions)
                _y_sub = self.domain.all_instance_vars()
                return unfold_basic_comprehension.instantiate(
                        {S:self.domain.domain, _Q_op:_Q_op_sub,
                         x:element, y:_y_sub})
            else:
                # multiple explicit conditions, so we use the And(*)
                # construction from earlier for the _Q_op_sub
                return unfold_basic_comprehension.instantiate(
                        {S:self.domain.domain, _Q_op:_Q_op_sub, x:element,
                         y:self.domain.all_instance_vars()[0]})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars
            _n_sub = num(len(self.domain.all_instance_vars()))
            _f_op, _f_op_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            if len(self.domain.explicit_conditions())<=1:
                should_auto_simplify = True
                # will simplify vacuous And() and trivial And(Q(y))
            else:
                should_auto_simplify = False
            return unfold.instantiate(
                {n:_n_sub, S:self.domain.all_domains(),
                _Q_op:_Q_op_sub, _f_op:_f_op_sub,
                x:element, y:self.domain.all_instance_vars()},
                auto_simplify = should_auto_simplify).derive_consequent()

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on a SetOfAllMembership object such as
        self = [elem in SetOfAll()], and depending on the form of self,
        derive and return self, knowing or assuming the rhs of the
        SetOfAll comprehension definition theorem (or the condition in
        the SetOfAll fold theorem):
        (1) From self = (x in {y}_{y in S}) and knowing or assuming
            that (x in S), derive and return self.
        (2) From self = (x in {y | Q(y)}_{y in S}) and knowing or
            assuming that ((x in S) AND (Q(x))), derive and return self.
        (3) From self = (x in {y | Q1(y), Q2(y),...,Qn(y)}_{y in S})
            and knowing or assuming that ((x in S) AND (Q1(x) and ...
            Qn(x))), derive and return self.
        (4) From self = (x in {f(y1,...,yn) | Q(y1,...yn)}_{y1 in S1,
            ...,yn in Sn}) and knowing or assuming that
            Exists_{y1 in S1,...,yn in Sn | Q(y1,...,yn)} such that
            [x = f(y1,...,yn)], derive and return self.

        There are some cases for which the method works only when
        called a second time on the same input. Not sure why.

        This method does not work for cases in which the underlying
        SetOfAll domain has both multiple instance variables
        and multiple explicit conditions simultaneously.
        '''

        from . import (fold, fold_basic_comprehension,
                       in_superset_if_in_comprehension)
        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())
        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)

        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # cases like [x in {y}_{y in S}]
            #         or [x in {y | Q(y)}_{y in S}]
            #         or [x in {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}]
            _S_sub = self.domain.domain
            _y_sub = self.domain.all_instance_vars()[0]
            return fold_basic_comprehension.instantiate(
                    {S:_S_sub, _Q_op:_Q_op_sub, x:element,
                     y:_y_sub})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars
            _n_sub = num(len(self.domain.all_instance_vars()))
            _f_op, _f_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            if len(self.domain.explicit_conditions())<=1:
                should_auto_simplify = True
                # will simplify vacuous And() and trivial And(Q(y))
            else:
                should_auto_simplify = False
            return fold.instantiate(
                {n:_n_sub, S:self.domain.all_domains(), 
                _Q_op:_Q_op_sub, _f_op:_f_sub,
                x:element, y:self.domain.all_instance_vars()},
                auto_simplify = should_auto_simplify).derive_consequent()

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (x in SetOfAll()) is in Bool. Used as 
        helper function elsewhere and not usually explicitly called
        by the user.
        '''
        from . import (comprehension_membership_is_bool,
                       comprehension_membership_is_bool_basic)

        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())
        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)
        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # simple case of [x in {y | Q(y)}_{y in S}]
            # or [x in {y | Q1(y), ..., Qn(y)}_{y in S}]:
            _S_sub = self.domain.domain # since only 1 instance var
            _y_sub = self.domain.all_instance_vars()[0]
            return comprehension_membership_is_bool_basic.instantiate(
                    {S:self.domain.domain, _Q_op:_Q_op_sub,
                         x:element, y:_y_sub})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars [?]
            _n_sub = num(len(self.domain.all_instance_vars()))
            _S_sub = self.domain.all_domains()
            _f_op, _f_op_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            _y_op_sub  = self.domain.all_instance_vars()
            if len(self.domain.explicit_conditions())<=1:
                should_auto_simplify = True
                # will simplify vacuous And() and trivial And(Q(y))
            else:
                should_auto_simplify = False
            return comprehension_membership_is_bool.instantiate(
                {n:_n_sub, S:_S_sub, _Q_op:_Q_op_sub, _f_op:_f_op_sub,
                x:element, y:_y_op_sub},
                auto_simplify = should_auto_simplify)


class SetOfAllNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in a set comprehension,
    i.e. non-membership in a SetOfAll construction.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for comprehension non-membership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return an equality depending on the form of the
        SetOfAll set comprehension serving as the (non)-domain.
        (1) From [x NotIn {y | Q(y)}_{y in S}], deduce and return
            [x NotIn {y|Q(y)}_{y in S}] = [(x NotIn S) OR Not(Q(x))].
        (2) From [x NotIn {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}],
            deduce and return
            [x NotIn {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}] =
            [(x NotIn S) OR Not(Q1(y)) and Q2(y),..., and Qn(y))].
        (3) From [x NotIn {f(y) | Q1(y),...,Qn(y)}]_{y in S}],
            deduce and return
            [x NotIn {f(y) | Q1(y),...,Qn(y)}]_{y in S}] = 
            Forall_{y in S | Q1(y),...,Qn(y)}[x NotEqual f(y)].
        In cases (2) and (3), the Q1(y),...,Qn(y) are interpreted
        as Q(y) = And(Q1(y),...,Qn(y)).

        Note: this method raises an error when the SetOfAllNonmembership
        expression has both multiple instance variables and multiple
        explicit conditions simultaneously.
        '''

        from . import nonmembership_equiv, nonmembership_equiv_basic

        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())

        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)

        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # simple case of [x in {y | Q(y)}_{y in S}]
            # or [x in {y | Q1(y), ..., Qn(y)}_{y in S}]:
            _S_sub = self.domain.all_domains()[0] # only 1 instance var
            _y_sub = self.domain.all_instance_vars()
            return nonmembership_equiv_basic.instantiate(
                    {S:_S_sub, _Q_op:_Q_op_sub, x:element, y:_y_sub})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars
            _n_sub = num(len(self.domain.all_instance_vars()))
            _f_op, _f_op_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            _S_sub = self.domain.all_domains()
            _y_sub = self.domain.all_instance_vars()
            # if len(self.domain.explicit_conditions())<=1:
            #     should_auto_simplify = True
            #     # will simplify vacuous And() and trivial And(Q(y))
            # else:
            #     should_auto_simplify = False
            return nonmembership_equiv.instantiate(
                {n:_n_sub, S:_S_sub, _Q_op:_Q_op_sub, _f_op:_f_op_sub,
                x:element, y:_y_sub})

    def as_defined(self):
        '''
        TBA. The idea here is to return (but do not derive) the
        'unfolded' version (i.e. the definition) of a
        SetOfAllNonmembership expression, depending on the form of the
        membership object:
        (1) From (x NotIn {y | Q(y)})_{y in S}, return
            [(x NotIn S) OR Not(Q(x))].
        (2) From (x NotIn {y | ..Q(y)..})_{y in S},
            return [(x NotIn S) OR (..Not(Q(x))..)].
        (3) From (x NotIn {f(y) | ..Q(y)..})_{y in S}, return
            Forall_{y in S | ...Q(y)...}[x NotEqual f(y)].
        In the case of a simple Union() membership, the disjunction of
        memberships is easily constructed and you might want such a
        definition without having to instantiate the unfold theorem
        and actually derive the definition result.
        In the case of a SetOfAllNonmembership, the situation is more
        complicated, with the explicit conditions potentially being
        quite varied.
        # From original UnionNonmembership:
        From self=[elem not in (A U B U ...)], return
        [(element not in A) and (element not in B) and ...].
        '''
        # code from original UnionNonmembership:
        # from proveit.logic import And, NotInSet
        # element = self.element
        # return And(*self.domain.operands.map_elements(
        #         lambda subset : NotInSet(element, subset)))

        raise NotImplementedError(
                "SetOfAllNonmembership.as_defined() not yet implemented.")

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on a SetOfAllNonmembership object such as
        self = [elem NotIn SetOfAll()], and depending on the form of
        the SetOfAll set comprehension serving as the (non)-domain,
        derive and return self, knowing or assuming the rhs of the
        SetOfAllNonmembership definition theorem:
        (1) From self = (x NotIn {y}_{y in S}) and knowing or
            assuming [(x NotIn S)], derive and return self.
        (2) From self = (x NotIn {y | Q(y)}_{y in S}) and knowing or
            assuming that ((x NotIn S) OR (Not(Q(x))), derive and
            return self.
        (3) From self = (x in {y | Q1(y), Q2(y),...,Qn(y)}_{y in S})
            and knowing or assuming that
            [(x NotIn S) OR Not(Q1(y)) and Q2(y),..., and Qn(y))],
            derive and return self.
        (4) From self = (x NotIn {f(y1,...,yn) | Q(y1,...yn)}_{y1 in S1,
            ...,yn in Sn}) and knowing or assuming that
            Forall_{y1 in S1,...,yn in Sn | Q(y1,...,yn)}[x NotEqual
            f(y1,...,yn)], derive and return self.

        There are some cases for which the method works only when
        called a second time on the same input. Not sure why.

        This method does not work for cases in which the underlying
        SetOfAll (non)-domain has both multiple instance variables
        and multiple explicit conditions simultaneously.
        '''

        from . import (nonmembership_fold, nonmembership_fold_basic)
        element = self.element

        if len(self.domain.explicit_conditions())==1:
            explicit_conditions = self.domain.explicit_conditions()[0]
        else:
            # which includes case of no explicit conditions!
            explicit_conditions = And(*self.domain.explicit_conditions())
        _Q_op, _Q_op_sub = (
                Function(Q, self.domain.all_instance_vars()),
                explicit_conditions)

        if (len(self.domain.all_instance_vars()) == 1 and
            self.domain.instance_element == self.domain.instance_var):
            # cases like [x NotIn {y}_{y in S}]
            #       or [x NotIn {y | Q(y)}_{y in S}]
            #       or [x NotIn {y | Q1(y), Q2(y),...,Qn(y)}_{y in S}]
            _S_sub = self.domain.domain
            _y_sub = self.domain.all_instance_vars()[0]
            return nonmembership_fold_basic.instantiate(
                    {S:_S_sub, _Q_op:_Q_op_sub, x:element,
                     y:_y_sub})
        else: 
            # cases where we have:
            # (1) multiple instance_vars,
            # (2) and/or instance_element is not just an instance_var
            # In fact, this doesn't yet work with multiple instance vars
            _n_sub = num(len(self.domain.all_instance_vars()))
            _f_op, _f_sub = (
                    Function(f, self.domain.all_instance_vars()),
                    self.domain.instance_element)
            if len(self.domain.explicit_conditions())<=1:
                should_auto_simplify = True
                # will simplify vacuous And() and trivial And(Q(y))
            else:
                should_auto_simplify = False
            return nonmembership_fold.instantiate(
                {n:_n_sub, S:self.domain.all_domains(), 
                _Q_op:_Q_op_sub, _f_op:_f_sub,
                x:element, y:self.domain.all_instance_vars()},
                auto_simplify = should_auto_simplify)
