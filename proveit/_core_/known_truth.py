"""
A KnownTruth represents an expression that has been proven to be a true
statement.  A KnownTruth wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from storage import storage
            
class KnownTruth:
    
    # lookup_dict maps Expressions to lists of KnownTruths for proving the 
    # Expression under various assumptions.  Excludes redundancies in which one set
    # of assumptions subsumes another.
    lookup_dict = dict()

    def __init__(self, expression, assumptions, proof):
        '''
        Create a KnownTruth with the given Expression, set of assumptions, and proof.  These
        should not be created manually but rather through the creation of Proofs which should
        be done indirectly via Expression/KnownTruth derivation-step methods.
        '''
        from proveit._core_.proof import Proof
        # do some type checking
        if not isinstance(expression, Expression):
            raise ValueError('The expression (expr) of a KnownTruth should be an Expression')
        for assumption in assumptions:
            if not isinstance(assumption, Expression):
                raise ValueError('Each assumption should be an Expression')
        if not isinstance(proof, Proof):
            raise ValueError('The proof of a KnownTruth should be a Proof')
        # initialize KnownTruth attributes
        self.expr = expression
        # store the assumptions as an ordered list (with the desired order for display)
        # and an unordered set (for convenience when checking whether one set subsumes another).
        self.assumptions = tuple(assumptions)
        self.assumptionsSet = frozenset(assumptions)
        self._proof = proof
        if self.expr in KnownTruth.lookup_dict:
            # Another known truth for this expression
            KnownTruth.lookup_dict[self.expr].append(self)
        else:
            # The first known truth recorded for this expression.
            KnownTruth.lookup_dict[self.expr] = [self]               
        # a unique representation for the KnownTruth comprises its expr and assumptions:
        self._unique_rep = hex(self.expr._unique_id) + ';[' + ','.join(hex(assumption._unique_id) for assumption in assumptions) + ']'
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)

    def __eq__(self, other):
        if isinstance(other, KnownTruth):
            return self._unique_id == other._unique_id
        else: return False # other must be an KnownTruth to be equal to self
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return self._unique_id

    def proof(self):
        '''
        Returns the most up-to-date proof of this KnownTruth.
        '''
        return self._proof
    
    def _updateObsoleteProofs(self):
        '''
        After a Proof is finished being constructed, check to see if
        any proofs for this KnownTruth are obsolete; the new proof
        might make an previous one obsolete, or it may be born
        obsolete itself.
        '''
        keptTruths = []
        bornObsolete = False
        for other in KnownTruth.lookup_dict[self.expr]:
            if other == self: continue # that's not an "other"
            if self.assumptionsSet.issubset(other.assumptionsSet):
                other._updateProof(self._proof) # use the new proof that does the job as well or better
            elif self.assumptionsSet.issuperset(other.assumptionsSet):
                # the new proof was born obsolete
                self._updateProof(other._proof) # use an old proof that does the job better
                bornObsolete = True
            else:
                keptTruths.append(other)
        if not bornObsolete:
            keptTruths.append(self)
        # Remove the obsolete KnownTruths from the lookup_dict
        KnownTruth.lookup_dict[self.expr] = keptTruths

    def _updateProof(self, newProof):
        '''
        Update the proof of this KnownTruth which has been made obsolete.
        Dependents of the old proof must also be updated.
        '''
        oldDependents = self._proof._dependents
        self._proof = newProof # set to the new proof
        for oldDependentProof in oldDependents:
            # remake the dependents and update their proofs
            dependentReplacement = oldDependentProof.remake()
            oldDependentProof.provenTruth._updateProof(dependentReplacement)
        else:
            self._proof = newProof # no dependents, just replace the proof

    def __setattr__(self, attr, value):
        '''
        KnownTruths should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).   Also,
        _proof is an exception which can be updated internally.
        '''
        if attr != '_proof' and attr in self.__dict__:
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value    

    def __getattr__(self, name):
        '''
        The KnownTruth aquires the attributes of its Expression, so it will act
        like the Expression except it has additional (or possibly overridden) attributes.
        '''
        # called only if the attribute does not exist in KnownTruth directly
        if name == 'png':
            raise AttributeError("Do not use the Expression version of the 'png' attribute.") 
        return getattr(self.expr, name)
    
    def __dir__(self):
        '''
        The KnownTruth aquires the attributes of its Expression as well as its
        own attributes.
        '''
        return sorted(set(self.__dict__.keys() + dir(self.expr)))

    @staticmethod
    def findKnownTruth(expression, assumptions):
        '''
        Try to find a KnownTruth for this expression that applies to
        the given set of assumptions (its assumptions are a subset
        of the given assumptions).  Return None if there is no match.
        '''
        if expression not in KnownTruth.lookup_dict:
            return None
        truths = KnownTruth.lookup_dict[expression]
        suitableTruths = []
        for truth in truths:
            if truth.assumptionsSet.issubset(assumptions):
                suitableTruths.append(truth)
        if len(suitableTruths)==0: return None # no suitable truth
        # return one wih the fewest assumptions
        return min(suitableTruths, key=lambda truth : len(truth.assumptions))

    def generalize(self, forallVars, domain=None, conditions=tuple()):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized KnownTruth.
        '''
        from proveit._core_.proof import Generalization
        from proveit import Variable
        if isinstance(forallVars, Variable):
            forallVars = [forallVars] # a single Variable to convert into a list of one
        return Generalization(self, forallVars, domain, conditions).provenTruth

    def asImplication(self, hypothesis):
        '''
        Performs a hypothetical reasoning derivation step, forming an
        implication statement with the given hypothesis and this statement
        as the conclusion.  The hypothesis is removed from the set of
        the conclusion statement's assumptions for the implication
        statement's assumptions.
        '''
        from proveit._core_.proof import HypotheticalReasoning
        if isinstance(hypothesis, KnownTruth):
            hypothesis = hypothesis.expr # we want the expression for this purpose
        return HypotheticalReasoning(self, hypothesis).provenTruth

    def relabel(self, relabelMap):
        '''
        Performs a relabeling derivation step, relabeling the Variables of the 
        KnownTruth for the expr and the assumptions.
        '''
        return Expression.relabel(self.expr, relabelMap, assumptions=self.assumptions)

    def asImpl(self, hypothesis):
        '''
        Abbreviation for asImplication.
        '''
        return self.asImplication(hypothesis)

    def latex(self):
        '''
        If the KnownTruth was proven under any assumptions, display the 
        double-turnstyle notation to show that the set of assumptions proves
        the statement/expression.  Otherwise, simply display the expression.
        '''
        if len(self.assumptions) > 0:
            return r'\{' + ','.join(assumption.latex() for assumption in self.assumptions) + r'\} \boldsymbol{\vdash} ' + self.expr.latex()
        return r'\boldsymbol{\vdash} ' + self.expr.latex()

    def string(self):
        '''
        If the KnownTruth was proven under any assumptions, display the 
        double-turnstyle notation to show that the set of assumptions proves
        the statement/expression.  Otherwise, simply display the expression.
        '''
        if len(self.assumptions) > 0:
            return r'{' + ','.join(assumption.string() for assumption in self.assumptions) + r'} |= ' + self.expr.string()
        return r'|= ' + self.expr.string()

    def __str__(self):
        '''
        Return a string representation of the KnownTruth.
        '''
        return self.string()

    def _repr_png_(self):
        '''
        Generate a png image from the latex.  May be recalled from memory or
        storage if it was generated previously.
        '''
        if not hasattr(self,'png'):
            self.png = storage._retrieve_png(self, self.latex(), self._config_latex_tool)
        return self.png # previous stored or generated
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
        for assumption in self.assumptions:
            assumption._config_latex_tool(lt)

    

