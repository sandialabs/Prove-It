from .label import Label
from proveit._core_.expression.expr import ImproperReplacement
from proveit._core_.defaults import USE_DEFAULTS

class Variable(Label):
    """
    A Variable is an interchangeable label.  They may be relabeled 
    Variable to Variable.  Through specialization of a Forall statement 
    over one or more Variables, those Variables may each be replaced 
    with a general Expression.
    """    
    def __init__(self, stringFormat, latexFormat=None):
        '''
        Create a Variable.  If latexFormat is not supplied, the stringFormat is used for both.
        '''
        Label.__init__(self, stringFormat, latexFormat, 'Variable')
                                        
    def _replaced(self, repl_map, allow_relabeling=False,
                  assumptions=USE_DEFAULTS, requirements=None,
                  equality_repl_requirements=None):
        '''
        Returns this Variable possibly replaced according to the 
        replacement map (repl_map) dictionary.  See the
        Expr.replaced documentation.
        '''
        from proveit._core_.expression.expr import Expression
        if len(repl_map)>0 and (self in repl_map):
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
                        %subbed)
            if not isinstance(subbed, Expression):
                raise TypeError('Must substitute a Variable with an '
                                'Expression (not %s)'%subbed.__class__)
            return subbed
        return self
        
    def _used_vars(self):
        return {self}
    
    def _free_var_ranges(self, exclusions=None):
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
        return {self:{self}}

    """
    def _free_vars(self, exclusions=frozenset()):
        if self in exclusions: 
            return set() # this is excluded
        return {self}
    
    def _check_param_occurrences(self, param_var, allowed_forms):
        '''
        When a Lambda expression introduces a variable in a new scope
        with a parameter entry that is an IndexedVar or a range
        of IndexedVars, its occurrences must all match that
        index or range exactly.  Raise a ValueError if the check fails.
        '''
        if self==param_var and self not in allowed_forms:
            # Invalid occurrence of the parameter variable.
            raise ValueError("Invalid occurrence of the parameter variable")
    """

def dummyVar(n):
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
    return Variable('_' + letters + '_', latexFormat = r'{_{-}' + letters + r'_{-}}')
    '''
    m = n
    powers_of_26 = [1, 26] # for 26 letters in the alphabet
    while m >= powers_of_26[-1]:
        m -= powers_of_26[-1]
        powers_of_26.append(powers_of_26[-1]*3)
    letters = ''
    powers_of_26.pop(-1)
    while len(powers_of_26) > 0:
        pow_of_26 = powers_of_26.pop(-1)
        k = int(m / pow_of_26)
        letters += chr(ord('a') + k)
        m -= k*pow_of_26
    return Variable('_' + letters, latexFormat = r'{_{-}' + letters + r'}')

def safeDummyVar(*expressions, start_index=0):
    usedVs = frozenset().union(*[expr._used_vars() for expr in expressions])
    i = start_index
    while dummyVar(i) in usedVs:
        i += 1
    return dummyVar(i)

def safeDummyVars(n, *expressions, start_index=0):
    dummyVars = []
    for _ in range (n):
        dummyVars.append(safeDummyVar(*(list(expressions)+list(dummyVars)),
                                      start_index=start_index))
    return dummyVars
            
def safeDefaultOrDummyVar(defaultVar, *expressions):
    usedVs = frozenset().union(*[expr._used_vars() for expr in expressions])
    if defaultVar not in usedVs:
        return defaultVar
    return safeDummyVar(*expressions)
