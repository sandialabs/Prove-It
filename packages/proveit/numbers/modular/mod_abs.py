from proveit import (defaults, Literal, Operation, 
                     relation_prover, equality_prover)
from proveit import a, b, c, i, j, L, N
from proveit.logic import Equals
from proveit.relation import TransRelUpdater
from proveit.numbers import (
        NumberOperation, Integer, Real, Add, ZeroSet,
        readily_provable_number_set)
from .mod import Mod

class ModAbs(NumberOperation):
    # operator of the ModAbs operation.
    _operator_ = Literal(string_format='ModAbs', theory=__file__)

    def __init__(self, value, divisor, *, styles=None):
        Operation.__init__(self, ModAbs._operator_, (value, divisor),
                           styles=styles)
        self.dividend = self.value = value
        self.divisor = divisor

    def string(self, **kwargs):
        return ('|' + self.value.string(fence=False) + '|_{mod ' +
                self.divisor.string(fence=False) + '}')

    def latex(self, **kwargs):
        return (r'\left|' + self.value.latex(fence=False)
                + r'\right|_{\textup{mod}\thinspace '
                  + self.divisor.latex(fence=False) + r'}')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Mod
        expression assuming the operands have been simplified.

        Specifically, performs reductions of the form
        |a mod L + b|_{mod L} = |a + b}_{mod L}.
        '''
        from . import (redundant_mod_elimination_in_modabs,
                       redundant_mod_elimination_in_sum_in_modabs)
        return Mod._redundant_mod_elimination(
                self, redundant_mod_elimination_in_modabs,
                redundant_mod_elimination_in_sum_in_modabs)

    @equality_prover('reversed_difference', 'reverse_difference')
    def difference_reversal(self, **defaults_config):
        '''
        Derive |a - b|_{N} = |b - a|_{N}.
        '''
        from proveit.numbers import Add, Neg
        from . import mod_abs_diff_reversal
        if not (isinstance(self.value, Add) and
                self.value.operands.is_double() and
                isinstance(self.value.operands[1], Neg)):
            raise ValueError(
                    "ModAbs.difference_reversal is only applicable for "
                    "an expression of the form |a - b|_{N}, not {0}".
                    format(self))
        _a_sub = self.value.operands[0]
        _b_sub = self.value.operands[1].operand
        _N_sub = self.divisor
        return mod_abs_diff_reversal.instantiate(
                {a:_a_sub, b:_b_sub, N: _N_sub})

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given ModAbs expression is in that
        number set using the appropriate closure theorem.
        '''
        import proveit.numbers.modular as mod_pkg

        thm = None
        if number_set == ZeroSet:
            divisor_ns = readily_provable_number_set(self.divisor)
            if Integer.readily_includes(divisor_ns):
                thm = mod_pkg.mod_abs_in_zero_set_int
            else:
                thm = mod_pkg.mod_abs_in_zero_set
        elif number_set == Integer:
            thm = mod_pkg.mod_abs_int_closure
        elif number_set == Real:
            thm = mod_pkg.mod_abs_real_closure
        if thm is not None:
            return thm.instantiate({a: self.value, b: self.divisor})
        raise NotImplementedError(
            "'ModAbs.deduce_in_number_set()' not implemented for the %s set"
            % str(number_set))

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        value_ns = readily_provable_number_set(self.value)
        divisor_ns = readily_provable_number_set(self.divisor)
        if value_ns == ZeroSet:
            return ZeroSet # |0|_{mod b} = 0
        elif value_ns.readily_includes(Integer) and (
                divisor_ns.readily_includes(Integer)):
            return Integer
        else:
            return Real
