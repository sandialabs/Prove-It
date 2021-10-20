from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.operation.function import Function
from proveit._core_.expression.composite import is_single
from proveit._core_.expression.label import Variable
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS


class IndexedVar(Function):
    '''
    An IndexedVar Expression expresses a Variable or nested IndexedVar,
    representing an ExprTuple (or ExprArray which is really just an ExprTuple
    of ExprTuples), being indexed to yield an element.  The indices are
    typically parameters of containing ExprRanges, or additively shifted
    versions of such parameters.  For example,
        (x_{1, 1+1} + ... + x_{1, j+1} + ... + x_{1, n+1}) * ... *
        (x_{i, 1+1} + ... + x_{i, j+1} + ... + x_{i, n+1}) * ... *
        (x_{m, 1+1} + ... + x_{m, j+1} + ... + x_{m, n+1})
    is represented by a doubly-nested ExprRange using the IndexedVar
    x_{i, j+1}.
    '''

    def __init__(self, var, index_or_indices, *, styles=None):
        '''
        Initialize an IndexedVar to represent the given 'var' being indexed
        via 'index_or_indices'.  The 'var' must be a Variable.
        '''
        from proveit._core_.expression.composite import composite_expression
        if not isinstance(var, Variable):
            raise TypeError("'var' being indexed should be a Variable "
                            "or IndexedVar itself; got %s" % str(var))
        self.indices = composite_expression(index_or_indices)
        if is_single(self.indices):
            # has a single index
            self.index = self.indices[0]
            self.index_or_indices = self.index
        else:
            self.index_or_indices = self.indices
        Function.__init__(self, var, self.index_or_indices, styles=styles)
        self.var = var

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if sub_class != IndexedVar:
            MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'IndexedVar':
            raise ValueError(
                "Expecting IndexedVar core_info to contain exactly"
                " one item: 'IndexedVar'")
        return IndexedVar(*sub_expressions, styles=styles)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.var
        yield self.index_or_indices

    def basic_replaced(self, repl_map, *,
                       allow_relabeling=False, requirements=None):
        '''
        Returns this expression with sub-expressions substituted
        according to the replacement map (repl_map) dictionary.
        '''
        if len(repl_map) > 0 and (self in repl_map):
            return repl_map[self]
        # First do a replacement after temporarily removing the base
        # variable from the repl_map so we can see if the result of
        # that is in the repl_map.
        base_var = self.var
        base_var_sub = repl_map.pop(base_var, None)
        replaced_sans_base_var_sub = \
            Expression.basic_replaced(self, repl_map, 
                                      allow_relabeling=allow_relabeling,
                                      requirements=requirements)
        if base_var_sub is None:
            # base_var wasn't in repl_map in the first place, so
            # attempting to remove it had no effect.
            return replaced_sans_base_var_sub
        try:
            if replaced_sans_base_var_sub in repl_map:
                return repl_map[replaced_sans_base_var_sub]
        finally:
            repl_map[base_var] = base_var_sub
        # As the last resort, do the replacement with the
        # base_var in the repl_map.
        return Expression.basic_replaced(
                self, repl_map, allow_relabeling=allow_relabeling,
                requirements=requirements)

    def _function_formatted(self, format_type, **kwargs):
        indices_str = self.index_or_indices.formatted(format_type, fence=False)
        result = self.var.formatted(format_type) + '_{' + indices_str + '}'
        if kwargs.get('force_fence', False):
            if format_type == 'latex':
                return r'\left(' + result + r'\right)'
            else:
                return '(' + result + ')'
        return result

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
        forms_dict = dict()
        forms_dict.update(
            self.indices._free_var_ranges(exclusions=exclusions))
        forms_dict.update({self.var: {self}})
        return forms_dict
