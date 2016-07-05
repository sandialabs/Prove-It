"""
A KnownTruth represents an expression that has been proven to be a true
statement.  A KnownTruth wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from proveit._core_.defaults_and_settings import storage
            
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
        # add the KnownTruth to KnownTruth.lookup_dict (unless it is redundant)
        if self.expr in KnownTruth.lookup_dict:
            # Another known truth for this expression.
            # Update proofs for any known truths that have become obsolete by this one
            # with a superset of this ones' assumptions.
            keptTruths = []
            for other in KnownTruth.lookup_dict[self.expr]:
                if self.assumptionsSet.issubset(other.assumptionsSet):
                    other._updateProof(proof) # use the new proof that is does the job as well or better
                else:
                    keptTruths.append(other)
            # Remove the obsolete KnownTruths from the lookup_dict
            KnownTruth.lookup_dict[self.expr] = keptTruths
            # See if this KnownTruth is born obsolete.
            preExistingReplacement = KnownTruth.findKnownTruth(expression, assumptions)
            if preExistingReplacement is not None:
                # this is a redundant known truth which is born with an existing replacement
                self._updateProof(preExistingReplacement._proof)
            else:
                # a new, non-redundant known truth.
                KnownTruth.lookup_dict[self.expr].append(self)
        else:
            # The first known truth recorded for this expression.
            KnownTruth.lookup_dict[self.expr] = [self]   

    def proof(self):
        '''
        Returns the most up-to-date proof of this KnownTruth.
        '''
        return self._proof

    def _updateProof(self, newProof):
        '''
        Update the proof of this KnownTruth which has been made obsolete.
        Dependents of the old proof must also be updated.
        '''
        from proof import Proof
        oldDependents = self._proof._dependents
        self._proof = newProof
        for oldDependentProof in oldDependents:
            dependentReplacement = Proof(oldDependentProof.provenTruth, oldDependentProof.requiredTruths())
            oldDependentProof.provenTruth._updateProof(dependentReplacement)

    def __setattr__(self, attr, value):
        '''
        KnownTruths should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).   Also,
        _proof is an exception which can be updated internally.
        '''
        if attr != '_proof' and hasattr(self, attr):
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value    

    def __getattr__(self, name):
        '''
        The KnownTruth aquires the attributes of its Expression, so it will act
        like the Expression except it has additional (or possibly overridden) attributes.
        '''
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
        exprStmts = KnownTruth.lookup_dict[expression]
        for stmt in exprStmts:
            if stmt.assumptionsSet.issubset(assumptions):
                return stmt # found one that works
        return None

    def generalize(self, forallVars, domain=None, conditions=tuple()):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized KnownTruth.
        '''
        from proveit._core_.proof import Generalization
        return Generalization(self, forallVars, domain, conditions).provenStmt

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
        return HypotheticalReasoning(self, hypothesis).provenStmt

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
            self.png = storage._retrieve_png(self, self._generate_png)
        return self.png # previous stored or generated
    
    def _generate_png(self):
        '''
        Compile the latex into a png image.
        '''
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        self.expr._config_latex_tool(lt)
        return latex_to_png(self.latex(), backend='dvipng', wrap=True)
    

