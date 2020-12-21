import sys
from proveit.statement import Literals, Operation, Variable, Multi_variable, STRING, LATEX
from proveit.theory import Theory
from proveit.basiclogic import Forall, Implies, In, NOTHING, multi_a, X, List

# quantum circuit literals
literals = Literals()
KLEENE_STAR = literals.add('KLEENE_STAR')


def _defineAxioms():
    # Forall_X [()] in X**
    _firstAxiom =\
        nullset_in_kleene = Forall(X, In(List(), KleeneRepetition(X)))
    # Forall_{A**, X} [A**] in X* => [A**, X] in X*
    concatenation_in_kleene = Forall([multi_a, X], Implies(
        In(List(multi_a), KleeneRepetition(X)), In(List(multi_a, X), KleeneRepetition(X))))
    return _firstAxiom, locals()


def _defineTheorems():
    # Forall_{A**, B**} ([A**] in X*) and ([B**] in X*) => [A**, B**] in X**
    _firstAxiom = combining_in_kleene = Forall([multi_a, X], Implies(
        In(List(multi_a), KleeneRepetition(X)), In(List(multi_a, X), KleeneRepetition(X))))
    return None


regular_expressions = Theory(
    sys.modules[__name__],
    literals,
    _defineAxioms,
    _defineTheorems)


class KleeneRepetition(Operation):
    """
    A Kleene repetition is used to express the set of zero or more of a particular thing
    (typically symbols or characters, the operand of this operation).  This is the Kleene
    star of a regular expression.
    """

    def __init__(self, operand):
        Operation.__init__(self, KLEENE_STAR, operand)

    def formatted(self, format_type, fenced=False):
        formatted_operand = self.operand.formatted(format_type, fenced=True)
        if format_type == STRING:
            return formatted_operand + '*'
        elif format_type == LATEX:
            return formatted_operand + '^{*}'

    def prove_in_repetition(self, repeating_list):
        pass  # TODO: Could do this with logarithmic efficiency using combining_in_kleene
