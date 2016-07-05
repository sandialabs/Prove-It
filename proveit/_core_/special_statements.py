'''
specialStatements

Methods for defining axioms and theorems.
'''

from expression.expr import Expression
from proveit._core_.proof import Axiom, Theorem

_excludedLocalVars = None
_specialStatementType = ''

def _beginSpecialStatements(excludedLocalVars, specialStatementType):
    global _excludedLocalVars, _specialStatementType
    _excludedLocalVars = set(excludedLocalVars.keys())
    _specialStatementType = specialStatementType

def _endSpecialStatements(localVars, specialStatementType, package):
    assert specialStatementType == _specialStatementType, 'cannot end ' + specialStatementType + ' without beggining them.'
    for name, expr in localVars.iteritems():
        '''
        For each non-excluded Expression, state it, mark it as an axiom/theorem, and replace the
        Expression in the localVars with the KnownTruth.
        '''
        if name in _excludedLocalVars: continue
        if name[0] == '_': continue # skip variables whose name begins with underscore
        assert isinstance(expr, Expression), 'Expecting only Expression statements for ' + _specialStatementType + ' variables.'
        if _specialStatementType == 'axioms':
            localVars[name] = Axiom(expr, package, name).provenTruth
        if _specialStatementType == 'theorems':
            localVars[name] = Theorem(expr, package, name).provenTruth   

def beginAxioms(excludedLocalVars):
    _beginSpecialStatements(excludedLocalVars, 'axioms')

def beginTheorems(excludedLocalVars):
    _beginSpecialStatements(excludedLocalVars, 'theorems')

def endAxioms(localVars, package):
    _endSpecialStatements(localVars, 'axioms', package)

def endTheorems(localVars, package):
    _endSpecialStatements(localVars, 'theorems', package)
    