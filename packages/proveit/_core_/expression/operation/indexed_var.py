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
    of ExprTuples), being indexed to yield an element.  The index must be
    is typically a parameter of a containing Iter.
    When IndexedVar's are nested, the default style is to display it as a 
    single variable with multiple indices.  That is,
    (x_i)_j will display, by default, as x_{i, j}.
    '''
    
    def __init__(self, var, index, flatten_nested_indexing=True):
        '''
        Initialize an IndexedVar to represent the given 'var' being indexed
        via 'index'.  The 'var' must be a Variable or an IndexedVar in a
        nested fashion.  The 'index' must be a Variable (typically the
        parameter of a containing Iter).  By default, nested indexed variables
        will display as a singe indexed variable with multiple indices,
        unless flatten_nested_indexing is False or the 'multi_indexed_var'
        style is changed.
        '''
        from proveit._core_.expression.composite.composite import compositeExpression
        from proveit._core_.expression.label.label import TemporaryLabel
        if not isinstance(var, Variable) and not isinstance(var, IndexedVar):
            if not isinstance(var, TemporaryLabel):
                raise TypeError("'var' being indexed should be a Variable "
                                "or IndexedVar itself; got %s"%str(var))
        if isinstance(var, IndexedVar):
            if flatten_nested_indexing:
                styles = {'multi_indexed_var':'flat'}
            else:
                styles = {'multi_indexed_var':'nested'}                
        else:
            styles = None
        
        self.index = index
        Operation.__init__(self, var, self.index, styles=styles)
        self.var = var
    
    def styleOptions(self):
        options = StyleOptions(self)
        if isinstance(self.var, IndexedVar):
            options.add('multi_indexed_var', 
                        ("'flat' or 'nested' to show multipe "
                         "indices or the true nested structure"))
        return options
    
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
        yield self.index
        if self.getStyle('multi_indexed_var', 'flat') == 'nested':
            yield ('flatten_nested_indexing', False)       
    
    def getBaseVar(self):
        '''
        Return the Variable being indexed, or if it is a nested IndexedVar,
        that of the nested IndexedVar until we get to the actual Variable.
        '''
        if isinstance(self.var, IndexedVar):
            return self.var.getBaseVar()
        return self.var
    
    def getIndices(self):
        '''
        Return the indices of the IndexedVar, starting from the inner-most
        nested IndexedVar going out.
        '''
        if isinstance(self.var, IndexedVar):
            return self.var.getIndices() + (self.index,)
        return (self.index,)
    
    def _formatted(self, formatType, **kwargs):
        if self.getStyle('multi_indexed_var', 'nested') == 'flat' and \
                isinstance(self.var, IndexedVar):
            indices_str = ','.join(index.formatted(formatType) 
                                   for index in self.getIndices())
            result = self.getBaseVar().formatted(formatType) + '_{'+indices_str+'}'
        else:
            index_str = self.index.formatted(formatType, fence=False)
            result = self.var.formatted(formatType, forceFence=True) + '_{' + index_str + '}'
        if kwargs.get('forceFence', False) == True:
            if formatType=='latex':
                return r'\left(' + result + r'\right)'
            else: return '(' + result + ')'
        return result

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

    def _free_indexed_vars(self, range_param):
        from proveit.number import const_shift_decomposition
        if self.index == range_param:
            return {self}
        else:
            index_base, shift = const_shift_decomposition(self.index)
            if index_base == range_param:
                return {self}
            return Expression._free_indexed_vars(self, range_param)
    
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
