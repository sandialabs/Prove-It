import sys
from proveit.statement import Literals, Operation, Variable, MultiVariable, STRING, LATEX
from proveit.theory import Theory
from proveit.basiclogic import Forall, Implies, In, NOTHING, multiA, X, List

# quantum circuit literals
literals = Literals()
KLEENE_STAR = literals.add('KLEENE_STAR')

def _defineAxioms():
    # Forall_X [()] in X**
    _firstAxiom =\
    nullsetInKleene = Forall(X, In(List(), KleeneRepetition(X)))
    # Forall_{A**, X} [A**] in X* => [A**, X] in X*
    concatenationInKleene = Forall([multiA, X], Implies(In(List(multiA), KleeneRepetition(X)), In(List(multiA, X), KleeneRepetition(X))))
    return _firstAxiom, locals()

def _defineTheorems():
    # Forall_{A**, B**} ([A**] in X*) and ([B**] in X*) => [A**, B**] in X**
    _firstAxiom =\
    combiningInKleene = Forall([multiA, X], Implies(In(List(multiA), KleeneRepetition(X)), In(List(multiA, X), KleeneRepetition(X))))
    return None

regular_expressions = Theory(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)

class KleeneRepetition(Operation):
    """
    A Kleene repetition is used to express the set of zero or more of a particular thing 
    (typically symbols or characters, the operand of this operation).  This is the Kleene
    star of a regular expression.
    """
    
    def __init__(self, operand):
        Operation.__init__(self, KLEENE_STAR, operand)
        
    def formatted(self, formatType, fenced=False):
        formatted_operand = self.operand.formatted(formatType, fenced=True)
        if formatType == STRING:
            return formatted_operand + '*'
        elif formatType == LATEX:
            return formatted_operand + '^{*}'
        
    def proveInRepetition(self, repeating_list):
        pass # TODO: Could do this with logarithmic efficiency using combiningInKleene
    
    