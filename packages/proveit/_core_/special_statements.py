'''
specialStatements

Methods for defining axioms and theorems.
'''

from expression.expr import Expression
from proveit._core_.proof import Axiom, Theorem
from proveit._core_.known_truth import KnownTruth

_excludedLocalVars = None
_specialStatementType = ''

def _beginSpecialStatements(excludedLocalVars, specialStatementType):
    global _excludedLocalVars, _specialStatementType
    _excludedLocalVars = dict(excludedLocalVars)
    _specialStatementType = specialStatementType

def _endSpecialStatements(localVars, specialStatementType, package):
    global _includedVars
    assert specialStatementType == _specialStatementType, 'cannot end ' + specialStatementType + ' without beggining them.'

    # exclude name/values in _excludedLocalVars or names that begin with an underscore
    includedVars = {name:val for name,val in localVars.iteritems() \
                    if _excludedLocalVars.get(name, None) is not val and name[0] != '_'}
    definitions = dict()
    for name, val in includedVars.iteritems():
        '''
        For each non-excluded Expression, state it, mark it as an axiom/theorem, and replace the
        Expression in the localVars with the KnownTruth.
        '''
        expr = val.expr if isinstance(val, KnownTruth) else val
        assert isinstance(expr, Expression), 'Expecting only Expression statements for ' + _specialStatementType + ' variables: ' + name
        if specialStatementType == 'axioms':
            localVars[name] = Axiom(expr, package, name).provenTruth
        if specialStatementType == 'theorems':
            localVars[name] = Theorem(expr, package, name).provenTruth   
        definitions[name] = localVars[name]

    for name, val in includedVars.iteritems():
        # Now derive side effects, after all the Axioms/Theorems have been created
        localVars[name].deriveSideEffects()
    
    return definitions

def beginAxioms(excludedLocalVars):
    _beginSpecialStatements(excludedLocalVars, 'axioms')

def beginTheorems(excludedLocalVars):
    _beginSpecialStatements(excludedLocalVars, 'theorems')

def endAxioms(localVars, package):
    from proveit.certify import setAxioms
    definitions = _endSpecialStatements(localVars, 'axioms', package)
    setAxioms(package, definitions)

def endTheorems(localVars, package):
    from proveit.certify import setTheorems
    definitions = _endSpecialStatements(localVars, 'theorems', package)
    setTheorems(package, definitions)
