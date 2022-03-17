from proveit import Function, Literal, relation_prover, equality_prover
from proveit import a
from proveit.numbers import deduce_number_set, NumberOperation

class Log(NumberOperation, Function):
    # operator of the Log operation.
    _operator_ = Literal(string_format='log', latex_format=r'\textrm{log}',
                         theory=__file__)    
    
    def __init__(self, base, antilog, *, styles=None):
        Function.__init__(self, Log._operator_, (base, antilog),
                          styles=styles)
        self.base = base
        self.antilog = antilog

    def string(self, **kwargs):
        return Log._operator_.string() + "_%s(%s)"%(
                self.base.string(), self.antilog.string())

    def latex(self, **kwargs):
        return Log._operator_.latex() + r"_%s\left(%s\right)"%(
                self.base.latex(), self.antilog.latex())

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        if self.base == self.antilog:
            from . import log_eq_1
            return log_eq_1.instantiate({a:self.base})
        return NumberOperation.shallow_simplification(
            self, must_evaluate=must_evaluate)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Attempt to prove that the logarithmic expression 'self' is
        in the given number set 'number_set'. May require user to
        previously show or assume that the Log base is not 1.
        Currently implemented only for the general case, giving
        Log_a(b) in Real when 'a' and 'b' both in RealPos and 'a' != 1.
        This can be augmented in near future.
        '''
        from proveit import a, b
        from proveit.logic import InSet, NotEquals
        from proveit.numbers.logarithms import log_real_pos_real_closure

        from proveit.numbers import zero, Real

        deduce_number_set(self.base)
        deduce_number_set(self.antilog)
        if number_set == Real:
            return log_real_pos_real_closure.instantiate(
                {a: self.base, b: self.antilog})

        # we can do more/better but that's enough for right now

        raise NotImplementedError(
            "'Log.deduce_in_number_set()' not implemented for the "
            " number set {0}. Try deducing in Real instead?".
            format(number_set))

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        For simple cases, deduce a bound on this Logarithmic (Log)
        object given a bound on its operand. For example, suppose
        x = Log(2, y) and we know that y >= 2. Then
        x.bound_via_operand_bound(y >= 2) returns x >= Log(2, 2) = 1.
        This method currently works MAINLY for expressions of the
        form Log(a, b) where a > 1, where we know something of the
        form b < y or b <= y or b > y or b >= y involving the 'antilog'
        argument b. b itself will also need to be in RealPos, which
        might need to be pre-proven or provided as an assumption.
        
        Future development should address cases where 0 < a < 1,
        which result in decreasing logarithmic functions.

        Also see NumberOperation.deduce_bound() and compare to the
        bound_via_operand_bound() method found in the Div, Neg, and
        Exp classes.
        '''
        from proveit import Judgment
        from proveit import a, x, y
        from proveit.numbers import (
                zero, one, 
                two, greater, greater_eq, Less, LessEq,
                NumberOrderingRelation, RealNonNeg)
        if isinstance(operand_relation, Judgment):
            operand_relation = operand_relation.expr
        if not isinstance(operand_relation, NumberOrderingRelation):
            raise TypeError(
                    "In Exp.bound_via_operand_bound(), the "
                    "'operand_relation' argument is expected to be a number "
                    "relation (<, >, ≤, or ≥), but instead was {}.".
                    format(operand_relation))

        lhs = operand_relation.lhs
        # should be able to generalize this later
        # no need to limit to just lhs, right?
        if lhs != self.antilog:
            raise ValueError(
                    "In Log.bound_via_operand_bound(), the left side of "
                    "the 'operand_relation' argument {0} is expected to "
                    "match the Log antilog operand {1}.".
                    format(operand_relation, self.antilog))

        # assign x and y subs according to std Less or LessEq relations
        _x_sub = operand_relation.normal_lhs
        _y_sub = operand_relation.normal_rhs
        _a_sub = self.base

        # Multiple cases to eventually consider but for now
        # we only consider four related Log(a, x) vs. Log(a, y)
        # cases for the increasing (base a > 1) version of a Log fxn:
        #  (1) base a > 1, 0 < x <  y 
        #  (2) base a > 1, 0 < x <= y
        #  (3) base a > 1, 0 < y < x
        #  (4) base a > 1, 0 < y <= x

        # Cases (1)-(4): 0 < x < y or 0 < y < x
        if ( greater(_a_sub, one).proven()
             and greater(_x_sub, zero).proven() ):
            if isinstance(operand_relation, Less):
                from proveit.numbers.logarithms import (
                        log_increasing_less)
                bound = log_increasing_less.instantiate(
                        {x: _x_sub, y: _y_sub, a: _a_sub})
            elif isinstance(operand_relation, LessEq):
                from proveit.numbers.logarithms import (
                        log_increasing_less_eq)
                bound = log_increasing_less_eq.instantiate(
                        {x: _x_sub, y: _y_sub, a: _a_sub})
            else:
                raise TypeError(
                    "In Log.bound_via_operand_bound(), the 'operand_relation' "
                    "argument is expected to be a 'Less', 'LessEq', 'greater', "
                    "or 'greater_eq' relation. Instead we have {}.".
                    format(operand_relation))

        else:
            raise ValueError(
                    "In calling Log.bound_via_operand_bound(), a "
                    "specific matching case was not found for {0}. "
                    "Check/confirm that {1} > 1 and {2} is a positive "
                    "Real".
                    format(self, _a_sub, _x_sub))

        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this Log expression in the most
        restrictive standard number set we can readily know.
        Currently just implemented for Reals, but should be able
        to augment this to allow more precise placement in
        RealPos vs. RealNeg for suitable base/antilog combinations.
        '''
        from proveit.numbers import Real, RealPos, Complex
        base_ns = deduce_number_set(self.base).domain
        antilog_ns = deduce_number_set(self.antilog).domain
        if RealPos.includes(base_ns) and RealPos.includes(antilog_ns):
            return self.deduce_in_number_set(Real)
        return self.deduce_in_number_set(Complex)
