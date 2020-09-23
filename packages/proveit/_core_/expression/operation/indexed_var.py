from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.operation.operation import Operation
from proveit._core_.expression.label import Variable
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS

class IndexedVar(Operation):
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
    
    def __init__(self, var, index_or_indices):
        '''
        Initialize an IndexedVar to represent the given 'var' being indexed
        via 'index_or_indices'.  The 'var' must be a Variable.  
        '''
        from proveit._core_.expression.composite import compositeExpression
        from proveit._core_.expression.label.label import TemporaryLabel
        if not isinstance(var, Variable):
            if not isinstance(var, TemporaryLabel):
                raise TypeError("'var' being indexed should be a Variable "
                                "or IndexedVar itself; got %s"%str(var))
        self.indices = compositeExpression(index_or_indices)
        if len(self.indices) == 1:
            # has a single index
            self.index = self.indices[0]
            self.index_or_indices = self.index
        else:
            self.index_or_indices = self.indices
        Operation.__init__(self, var, self.index_or_indices)
        self.var = var
        
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != IndexedVar: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'IndexedVar':
            raise ValueError("Expecting IndexedVar coreInfo to contain exactly"
                             " one item: 'IndexedVar'")
        return IndexedVar(*subExpressions).withStyles(**styles)       

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.var
        yield self.index_or_indices
    
    def _replaced(self, repl_map, allow_relabeling,
                  assumptions, requirements,
                  equality_repl_requirements):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary.
        '''
        if len(repl_map)>0 and (self in repl_map):
            return repl_map[self]
        # First do a replacement after temporarily removing the base 
        # variable from the repl_map so we can see if the result of
        # that is in the repl_map.
        base_var = self.var
        base_var_sub = repl_map.pop(base_var, None)
        replaced_sans_base_var_sub = \
            Expression._replaced(self, repl_map, allow_relabeling, 
                                 assumptions, requirements,
                                 equality_repl_requirements)
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
        return Expression._replaced(self, repl_map, allow_relabeling, 
                                    assumptions, requirements,
                                    equality_repl_requirements)
    
    def _formatted(self, formatType, **kwargs):
        indices_str = self.index_or_indices.formatted(formatType, fence=False)
        result = self.var.formatted(formatType) + '_{' + indices_str + '}'
        if kwargs.get('forceFence', False) == True:
            if formatType=='latex':
                return r'\left(' + result + r'\right)'
            else: return '(' + result + ')'
        return result
    
    """
    def _free_var_indices(self):
        '''
        Returns a dictionary that maps indexed variables to
        a tuple with (start_base, start_shifts, end_base, end_shifts)
        indicating the indices for which an indexed variable is free.
        The start_shifts and end_shifts are constant integers.
        The included indices are each start_base + start_shift,
        each end_base + end_shift plus the range going from
        start_base + max(start_shifts) .. end_base + min(end_shifts).
        '''
        from proveit.number import const_shift_decomposition
        index_base, index_shift = const_shift_decomposition(self.index)
        # The start and end are the same so we have repetition below.
        return {self.var:(index_base, {index_shift}, 
                          index_base, {index_shift})}
    """

    def _possibly_free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free or 
        not explicitly and completely masked.  Examples of "forms":
            x
            x_i
            x_1, ..., x_n
            x_{i, 1}, ..., x_{i, n_i}
            x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}
        '''
        if exclusions is not None and self in exclusions: 
            return dict() # this is excluded
        forms_dict = dict()
        forms_dict.update(
                self.indices._possibly_free_var_ranges(exclusions=exclusions))
        forms_dict.update({self.var:{self}})
        return forms_dict
    
    
    """
    def _indexed_var_shifts(self, var, range_param, shifts):
        if self.var==var:
            shift = self._indexed_var_shift(range_param)
            if shift is not None:
                shifts.add(shift)
            return
        Expression._indexed_var_shifts(self, var, range_param, shifts)

    def _indexed_var_shift(self, range_param):
        '''
        If the IndexedVar's index is a const-shifted form of
        'range_param', return the shift.  Otherwise, return None.
        For "const-shifted", use the convention that the constant
        shift comes after (e.g., "k+1" rather than "1+k").
        '''
        from proveit.number import const_shift_decomposition
        index_base, shift = const_shift_decomposition(self.index)
        if index_base == range_param:
            return shift
        return None
    """

 