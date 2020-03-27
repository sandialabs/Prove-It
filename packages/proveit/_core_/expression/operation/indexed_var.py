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
        if not isinstance(var, Variable) and not isinstance(var, IndexedVar):
            raise TypeError("'var' being indexed should be a Variable an IndexedVar"
                            "itself, got %s"%str(var))
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
        if self.getStyle('multi_indexed_var', None) == 'nested':
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
        if self.getStyle('multi_indexed_var', None) == 'flat' and \
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

    def freeIndexedVars(self, index):
        if self.index == index:
            return {self}
        else:
            return set()
