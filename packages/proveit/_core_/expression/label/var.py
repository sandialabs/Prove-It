from .label import Label
from proveit._core_.expression.expr import ImproperReplacement
from proveit._core_.defaults import USE_DEFAULTS


class Variable(Label):
    """
    A Variable is an interchangeable label.  They may be relabeled
    Variable to Variable.  Through instantiation of a Forall statement
    over one or more Variables, those Variables may each be replaced
    with a general Expression.
    """

    def __init__(self, string_format, latex_format=None, *,
                 fence_when_forced=False, styles=None):
        '''
        Create a Variable.  If latex_format is not supplied, the string_format is used for both.
        '''
        Label.__init__(self, string_format, latex_format, 'Variable',
                       fence_when_forced=fence_when_forced, styles=None)

    def basic_replaced(self, repl_map, *,
                       allow_relabeling=False, requirements=None):
        '''
        Returns this Variable possibly replaced according to the
        replacement map (repl_map) dictionary.  See the
        Expr.replaced documentation.
        '''
        from proveit._core_.expression.expr import Expression
        if len(repl_map) > 0 and (self in repl_map):
            subbed = repl_map[self]
            if isinstance(subbed, set):
                # We surmise that this is a substitution of a range
                # of variables which must only reside in IndexedVar's of
                # an ExprRange over a  matching range of indices to be a
                # proper replaced.
                raise ImproperReplacement(
                    self, repl_map,
                    "Replacing a range of parameters can only be "
                    "performed when the parameter variable is only "
                    "ever contained in an IndexedVar with indices "
                    "iterated over the same range as the iterated "
                    "parameter, %s "
                    "(see Lambda.apply documentation)"
                    % subbed)
            if not isinstance(subbed, Expression):
                raise TypeError('Must substitute a Variable with an '
                                'Expression (not %s)' % subbed.__class__)
            return subbed
        return self

    def _used_vars(self):
        return {self}

    def _free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free
        (not within a lambda map that parameterizes the base variable).
        Examples of "forms":
            x
            x_i
            x_1, ..., x_n
            x_{i, 1}, ..., x_{i, n_i}
            x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}
        '''
        if exclusions is not None and self in exclusions:
            return dict()  # this is excluded
        return {self: {self}}


def dummy_var(n):
    '''
    Given an integer n, produce a "dummy" Variable that is the (n+1) element
    in the list: _X_, _Y_, _Z_, _XX_, _XY_, _XZ_, _YX_, _YY_, _YZ_, etc.
    '''
    '''
    m = n
    powers_of_3 = [1, 3]
    while m >= powers_of_3[-1]:
        m -= powers_of_3[-1]
        powers_of_3.append(powers_of_3[-1]*3)
    letters = ''
    powers_of_3.pop(-1)
    while len(powers_of_3) > 0:
        pow_of_3 = powers_of_3.pop(-1)
        k = int(m / pow_of_3)
        letters += chr(ord('x') + k)
        m -= k*pow_of_3
    return Variable('_' + letters + '_', latex_format = r'{_{-}' + letters + r'_{-}}')
    '''
    m = n
    powers_of_26 = [1, 26]  # for 26 letters in the alphabet
    while m >= powers_of_26[-1]:
        m -= powers_of_26[-1]
        powers_of_26.append(powers_of_26[-1] * 3)
    letters = ''
    powers_of_26.pop(-1)
    while len(powers_of_26) > 0:
        pow_of_26 = powers_of_26.pop(-1)
        k = int(m / pow_of_26)
        letters += chr(ord('a') + k)
        m -= k * pow_of_26
    return Variable('_' + letters, latex_format=r'{_{-}' + letters + r'}')


def safe_dummy_var(*expressions, start_index=0):
    used_vs = frozenset().union(*[expr._used_vars() for expr in expressions])
    i = start_index
    while dummy_var(i) in used_vs:
        i += 1
    return dummy_var(i)


def safe_dummy_vars(n, *expressions, start_index=0):
    dummy_vars = []
    for _ in range(n):
        dummy_vars.append(safe_dummy_var(
            *(list(expressions) + list(dummy_vars)), start_index=start_index))
    return dummy_vars


def safe_default_or_dummy_var(default_var, *expressions):
    used_vs = frozenset().union(*[expr._used_vars() for expr in expressions])
    if default_var not in used_vs:
        return default_var
    return safe_dummy_var(*expressions)
