"""
A KnownTruth represents an expression that has been proven to be a true
statement.  A KnownTruth wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from proveit._core_._unique_data import meaningData, styleData
from defaults import defaults, USE_DEFAULTS
import re

class _ExprProofs:
    '''
    Stores a set of proofs for a particular expression under any set
    of assumptions.  We maintain such sets so that we can update
    KnownTruth proofs appropriately when a particular proof has been
    disabled.
    '''
    all_expr_proofs = dict() # map expressions to expression proofs
        
    def __init__(self, expr):
        self._expr = expr
        self._proofs = set()
        _ExprProofs.all_expr_proofs[expr] = self
    
    def insert(self, newproof):
        '''
        Insert a new proof for the expression, maintaining sorted order
        in the proof size (number of steps).
        '''
        from proof import Proof
        assert isinstance(newproof, Proof)
        assert newproof.provenTruth.expr == self._expr
        self._proofs.add(newproof)
    
    def discard(self, oldproof):
        from proof import Proof
        assert isinstance(oldproof, Proof)
        assert oldproof.provenTruth.expr == self._expr
        assert not oldproof.isUsable(), "Should only remove unusable proofs"
        self._proofs.discard(oldproof)
    
    def bestProof(self, knowntruth):
        '''
        Return the best proof applicable to the knowntruth that is usable
        (or None if there aren't any that are usable).
        '''
        assert isinstance(knowntruth, KnownTruth)
        best_unusable_proof = None
        fewestSteps = float('inf')
        for proof in self._proofs:
            if proof.provenTruth.assumptionsSet.issubset(knowntruth.assumptionsSet):
                assert proof.isUsable(), 'unusable proofs should have been removed'
                
                if proof.numSteps() < fewestSteps:
                    fewestSteps = proof.numSteps()
                    best_unusable_proof = proof
        return best_unusable_proof # the proof with the fewest steps that is applicable

            
class KnownTruth:
    # lookup_dict maps Expressions to lists of KnownTruths for proving the 
    # Expression under various assumptions.  Excludes redundancies in which one set
    # of assumptions subsumes another.
    lookup_dict = dict()
    
    # Call the beginProof method to begin a proof of a Theorem.
    theoremBeingProven = None # Theorem being proven.
    hasBeenProven = None # Has the theoremBeingProven been proven yet in this session?  
                         # Goes from None to False (after beginning a proof and disabling Theorems that cannot be used)
                         # to True (when there is a legitimate proof).
    # Set of theorems/packages that are presumed to be True for the purposes of the proof being proven:
    presumingTheorems = None # set of Theorem objects when in use
    presumingPrefixes = None # set of context names or full theorem names when in use.
    qedInProgress = False # set to true when "%qed" is in progress

    # KnownTruths for which deriveSideEffects is in progress, tracked to prevent infinite
    # recursion when deducing side effects after something is proven.
    in_progress_to_derive_sideeffects = set() 


    def __init__(self, expression, assumptions, proof):
        '''
        Create a KnownTruth with the given Expression, set of as_sumptions, and proof.  These
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
        
        # note: these contained expressions are subject to style changes on a KnownTruth instance basis
        self.expr = expression
        # store the assumptions as an ordered list (with the desired order for display)
        # and an unordered set (for convenience when checking whether one set subsumes another).
        self.assumptions = tuple(assumptions)
        self.assumptionsSet = frozenset(assumptions)

        # The meaning data is shared among KnownTruths with the same structure disregarding style
        self._meaningData = meaningData(self._generate_unique_rep(lambda expr : hex(expr._meaning_id)))
        if not hasattr(self._meaningData, '_exprProofs'):
            # create or assign the _ExprProofs object for storing all proofs
            # for this KnownTruth's expr (under any set of assumptions).
            if self.expr in _ExprProofs.all_expr_proofs:
                exprProofs = _ExprProofs.all_expr_proofs[self.expr]
            else:
                exprProofs = _ExprProofs(self.expr)
            self._meaningData._exprProofs = exprProofs
            # Initially, _proof is None but will be assigned and updated via _addProof()
            self._meaningData._proof = None
        
        # The style data is shared among KnownTruths with the same structure and style.
        self._styleData = styleData(self._generate_unique_rep(lambda expr : hex(expr._style_id)))
        
        # establish some parent-child relationships (important in case styles are updated)
        self._styleData.addChild(self, self.expr)
        for assumption in self.assumptions:
            self._styleData.addChild(self, assumption)
        
        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaningData._unique_id
        self._exprProofs = self._meaningData._exprProofs
        
        self._style_id = self._styleData._unique_id
        
        # The _proof can change so it must be accessed via indirection into self._meaningData
        # (see proof() method).
    
    def _generate_unique_rep(self, objectRepFn):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        return objectRepFn(self.expr) + ';[' + ','.join(objectRepFn(assumption) for assumption in self.assumptions) + ']'

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        # Everything between the punctuation, ';', '[', ']', ',', is a represented object.
        objIds =  re.split(";|\[|,|\]",unique_rep)
        return [objId for objId in objIds if len(objId) > 0]           
                
    def deriveSideEffects(self):
        '''
        Derive any side-effects that are obvious consequences arising from this truth.
        Called after the corresponding Proof is complete.
        '''
        if not defaults.automation:
            return # automation disabled
        if self not in KnownTruth.in_progress_to_derive_sideeffects:
            # avoid infinite recursion by using in_progress_to_deduce_sideeffects
            KnownTruth.in_progress_to_derive_sideeffects.add(self)
            for sideEffect in self.expr.sideEffects(self):
                # Attempt each side-effect derivation, specific to the
                # type of Expression.
                try:
                    # use the default assumptions which are temporarily set to the
                    # assumptions utilized in the last derivation step.
                    sideEffect(assumptions=defaults.assumptions)     
                except:
                    pass
            KnownTruth.in_progress_to_derive_sideeffects.remove(self)        

    def __eq__(self, other):
        if isinstance(other, KnownTruth):
            return self._meaning_id == other._meaning_id
        else: return False # other must be an Expression to be equal to self
    
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id
        
    def beginProof(self, presuming=tuple()):
        '''
        Begin a proof for a theorem.  Only use other theorems that are in 
        the presuming list of theorems/packages or theorems that are required,
        directly or indirectly, in proofs of theorems that are explicitly 
        listed (these are implicitly presumed).  If there exists any 
        presumed theorem that has a direct or indirect dependence upon this 
        theorem then a CircularLogic exception is raised. 
        '''
        if KnownTruth.theoremBeingProven is not None:
            raise ProofInitiationFailure("May only beginProof once per Python/IPython session.  Restart the notebook to restart the proof.")
        from proof import Theorem
        theorem = self.proof() # the trivial proof-by-theorem; not yet the actual, desired proof of the theorem
        if not isinstance(theorem, Theorem):
            raise TypeError('Only begin a proof for a Theorem')
        theorem.recordPresumingInfo(presuming)
        print "Recorded 'presuming' information"
                
        presumed_theorems, presumed_contexts = set(), set()
        theorem.getRecursivePresumingInfo(presumed_theorems, presumed_contexts)
        explicit_presumed_theorems = set(presumed_theorems)
        explicit_presumed_contexts = set(presumed_contexts)
        
        # presume all previous theorems and their dependencies
        context = theorem.context
        num_prev_thms = 0 # number of previous theorems within the context
        for prev_thm_name in context.theoremNames():
            if prev_thm_name == theorem.name:
                break # concludes all "previous" theorems of the context
            thm = context.getTheorem(prev_thm_name)
            presumed_theorems.add(thm)
            if thm.hasProof():
                # presume dependencies of presumed theorems
                presumed_contexts.update(thm.allUsedTheorems())
            num_prev_thms += 1
        
        KnownTruth.theoremBeingProven = theorem
        KnownTruth.presumingTheorems = set(presumed_theorems)
        KnownTruth.presumingPrefixes = set(presumed_contexts)
        Theorem.updateUsability()
        
        # change KnownTruth.hasBeenProven
        # from None to False -- we can now test to see if 
        # we have a proof for KnownTruth.theoremBeingProven
        KnownTruth.hasBeenProven = False        
        
        """
        # check to see if the theorem was already proven before we started
        for proof in theorem._possibleProofs:
            if proof.isUsable():
                proof.provenTruth._recordBestProof(proof)
                return self.expr
        """
        if self._checkIfReadyForQED(self.proof()):
            return self.expr # already proven
        if len(explicit_presumed_contexts) > 0:
            print "Presuming theorems in %s (except any that depend upon this theorem)."%', '.join(sorted(explicit_presumed_contexts))
        if len(explicit_presumed_theorems) > 0:
            print "Presuming %s theorem(s) (and any of their dependencies)."%', '.join(sorted(str(thm) for thm in explicit_presumed_theorems))
        if num_prev_thms > 0:
            print "Presuming previous theorem(s) in this context (and any of their dependencies)."
        theorem._meaningData._unusableProof = theorem # can't use itself to prove itself
        return self.expr
    
    def _qed(self):
        '''
        Complete a proof that began via `beginProof`, entering it into
        the certification database.
        '''
        if KnownTruth.theoremBeingProven is None:
            raise Exception('No theorem being proven; cannot call qed method')
        if self.expr != KnownTruth.theoremBeingProven.provenTruth.expr:
            raise Exception('qed does not match the theorem being proven')
        if len(self.assumptions) > 0:
            raise Exception('qed proof should not have any remaining assumptions')
        KnownTruth.qedInProgress = True
        proof = self.expr.prove().proof()
        if not proof.isUsable():
            proof.provenTruth.raiseUnusableProof()
        KnownTruth.theoremBeingProven.recordProof(proof)
        KnownTruth.qedInProgress = False
        return proof

    def proof(self):
        '''
        Returns the most up-to-date proof of this KnownTruth.
        '''
        return self._meaningData._proof
    
    def isUsable(self):
        '''
        Returns True iff this KnownTruth has a "usable" proof.  Proofs
        may be unusable when proving a theorem that is restricted with
        respect to which theorems may be used (to avoid circular logic).
        '''
        proof = self.proof()
        return proof is not None and proof.isUsable()
    
    def isSufficient(self, assumptions):
        '''
        Return True iff the given assumptions satisfy the KnownTruth; 
        the KnownTruth is usable and requires a subset of the given assumptions.
        '''
        return self.isUsable() and self.assumptionsSet.issubset(assumptions)
    
    def asTheoremOrAxiom(self):
        '''
        Assuming this KnownTruth represents a Theorem or Axiom, return 
        the Theorem or Axiom object.
        '''
        from proof import Theorem, Axiom
        # Get the theorem associated with the KnownTruth (or raise an exception if there is none)
        if KnownTruth.theoremBeingProven is not None:
            if self.expr == KnownTruth.theoremBeingProven.provenTruth.expr:
                return KnownTruth.theoremBeingProven
        proof = self.proof()
        if isinstance(proof, Theorem) or isinstance(proof, Axiom):
            return proof
        else:
            raise ValueError("KnownTruth does not represent a theorem or axiom.")
    
    def printRequirements(self):
        '''
        Provided that this KnownTruth is known to represent a proven theorem,
        print the set of axioms that are required directly or indirectly in
        its proof as well as any required theorems that are unproven (if it
        has not yet been proven completely).
        '''
        from proveit.certify import isFullyProven, allRequirements
        # print the required axioms and unproven theorems 
        requiredAxioms, requiredTheorems = allRequirements(self)
        for axiom in sorted(requiredAxioms):
            print axiom
        if len(requiredTheorems) == 0:
            assert isFullyProven(self), "certification database is corrupt"
            print "Theorem is fully proven!"
        if len(requiredTheorems) > 0:
            assert not isFullyProven(self), "certification database is corrupt"
            print "\nUnproven theorems:"
            for theorem in sorted(requiredTheorems):
                print theorem

    def printDependents(self):
        '''
        Provided that this KnownTruth is known to represent a theorem or axiom,
        print all theorems that are known to depend on it directly or indirectly.
        '''
        from proveit.certify import allDependents
        dependents = allDependents(self)
        for theorem in sorted(dependents):
            print theorem
    
    def _discardProof(self, proof):
        '''
        Discard a disabled proof as an option in the _ExprProofs object.
        Don't change self._meaningData._proof, now, however.  It will be updated
        in due time and may be replaced with a proof that hasn't
        been disabled.
        '''
        self._exprProofs.discard(proof)
        
    def _addProof(self, newproof=None):
        '''
        After a Proof is finished being constructed, record the best
        proof for the KnownTruth which may be the new proof, 'proof',
        or a pre-existing one.  Update all KnownTruths
        with the same 'truth' expression that should be updated.
        '''
        #print 'record best', self.expr, 'under', self.assumptions
        # update KnownTruth.lookup_dict and use find all of the KnownTruths
        # with this expr to see if the proof should be updated with the new proof.

        if not newproof.isUsable():
            # Don't bother with a disabled proof unless it is the only
            # proof.  in that case, we record it so we can generate a useful
            # error message via raiseUnusableProof(..).
            if self._meaningData._proof is None:
                self._meaningData._proof = newproof
            return 
        self._exprProofs.insert(newproof)
    
        # Check to see if the new proof is applicable to any other KnownTruth.
        # It can replace an old proof if it became unusable or if the newer one uses fewer steps.
        expr_known_truths = KnownTruth.lookup_dict.setdefault(self.expr, [])
        expr_known_truths.append(self)
        for expr_known_truth in expr_known_truths:
            # Is 'proof' applicable to 'expr_known_truth'?
            if newproof.provenTruth.assumptionsSet.issubset(expr_known_truth.assumptionsSet):
                # replace if there was no pre-existing usable proof or the new proof has fewer steps
                preexisting_proof = expr_known_truth.proof()
                if preexisting_proof is None or not preexisting_proof.isUsable() or newproof.numSteps()<preexisting_proof.numSteps():
                    expr_known_truth._updateProof(newproof) # replace an old proof
    
    def _reviseProof(self):
        '''
        After a proof and its dependents have been disabled, we will see
        if there is another proof that is usable (see Proof.disable()).
        Return True iff the proof actually changed to something usable.
        '''
        return self._updateProof(self._exprProofs.bestProof(self))             
        
        
    """
    def _recordBestProof(self, newProof):
        '''
        After a Proof is finished being constructed, check to see if
        any proofs for this KnownTruth are obsolete; the new proof
        might make a previous one obsolete, or it may be born
        obsolete itself.  A proof is obsolete if there exists a KnownTruth
        with a subset of the assumptions required for that proof, or with
        the same set of assumptions but fewer steps.  A tie goes to the
        new proof, but note that the step number comparison will prevent
        anything cyclic (since a proof for a KnownTruth that requires that
        same KnownTruth as a dependent will necessarily include the
        number of steps of the original proof plus more).
        '''
        self._updateProof(self._exprProofs.bestProof(self))
        
        
        from proof import Theorem
        if not self.expr in KnownTruth.lookup_dict:
            # the first KnownTruth for this Expression
            self._proof = newProof
            KnownTruth.lookup_dict[self.expr] = [self]
            return
        if not newProof.isUsable():
            # if it is not usable, we're done.
            if self._proof is None:
                # but first set _proof to the newProof if there 
                # is not another one.
                self._proof = newProof
            return
        keptTruths = []
        bornObsolete = False
        for other in KnownTruth.lookup_dict[self.expr]:
            if self.assumptionsSet == other.assumptionsSet:
                if not other._proof.isUsable():
                    # use the new proof since the old one is unusable.
                    other._updateProof(newProof)
                elif newProof.numSteps <= other._proof.numSteps:
                    if newProof.requiredProofs != other._proof.requiredProofs:
                        # use the new (different) proof that does the job as well or better
                        if isinstance(newProof, Theorem):
                            # newer proof is a theorem; record the existing proof as a possible proof for that theorem
                            newProof._possibleProofs.append(other._proof)
                        other._updateProof(newProof)
                else:
                    # the new proof was born obsolete, taking more steps than an existing one
                    if isinstance(other._proof, Theorem):
                        # the older proof is a theorem, record the new proof as a possible proof for that theorem
                        other._proof._possibleProofs.append(newProof)
                    self._proof = other._proof # use an old proof that does the job better
                    keptTruths.append(other)
                    bornObsolete = True
            elif self.assumptionsSet.issubset(other.assumptionsSet):
                # use the new proof that does the job better
                other._updateProof(newProof) 
            elif self.assumptionsSet.issuperset(other.assumptionsSet) and other._proof.isUsable():
                # the new proof was born obsolete, requiring more assumptions than an existing one
                self._proof = other._proof # use an old proof that does the job better
                keptTruths.append(other)
                bornObsolete = True
            else:
                # 'other' uses a different, non-redundant set of assumptions or 
                # uses a subset of the assumptions but is unusable
                keptTruths.append(other)
        if not bornObsolete:
            if KnownTruth.theoremBeingProven is not None:
                if not KnownTruth.qedInProgress and len(self.assumptions)==0 and self.expr == KnownTruth.theoremBeingProven.provenTruth.expr:
                    if not KnownTruth.hasBeenProven:
                        KnownTruth.hasBeenProven = True
                        print '%s has been proven. '%self.asTheoremOrAxiom().name, r'Now simply execute "%qed".'
            self._proof = newProof
            keptTruths.append(self)
        # Remove the obsolete KnownTruths from the lookup_dict -- SHOULD ACTUALLY KEEP OLD PROOFS IN CASE ONE IS DISABLED -- TODO
        KnownTruth.lookup_dict[self.expr] = keptTruths
    """

    def _updateProof(self, newProof):
        '''
        Update the proof of this KnownTruth.  Return True iff the proof actually changed to something usable.
        '''
        meaningData = self._meaningData
        
        if newProof is None:
            # no usable proof.  
            # no need to update dependencies because that would have already been done when the proof was disabled.
            if meaningData._proof is not None:
                assert not meaningData._proof.isUsable(), "should not update to an unusable new proof if the old one was usable"
            return False # did not change to something usable
        assert newProof.isUsable(), "Should not update with an unusable proof"
        
        self._checkIfReadyForQED(newProof)
        
        if meaningData._proof is None:
            # no previous dependents to update
            meaningData._proof = newProof
            return True # new usable proof
        elif meaningData._proof == newProof:
            return False # no change
                
        # swap out the old proof for the new proof in all dependencies
        meaningData._proof._updateDependencies(newProof)
        meaningData._proof = newProof # set to the new proof
        
        return True
    
    def _checkIfReadyForQED(self, proof):
        if proof.isUsable() and proof.provenTruth==self:
            if KnownTruth.hasBeenProven is not None:
                # check if we have a usable proof for the theorem being proven
                if not KnownTruth.qedInProgress and len(self.assumptions)==0 and self.expr == KnownTruth.theoremBeingProven.provenTruth.expr:
                    if not KnownTruth.hasBeenProven:
                        KnownTruth.hasBeenProven = True
                        print '%s has been proven. '%self.asTheoremOrAxiom().name, r'Now simply execute "%qed".'
                        return True
        return False
    
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
        When accessing functions of the Expression, if that function has 'assumptions'
        as a keyword argument, the assumptions of the KnownTruth are automatically
        included.
        '''
        from proveit import defaults, USE_DEFAULTS
        import inspect
        
        # called only if the attribute does not exist in KnownTruth directly
        if name == 'png':
            raise AttributeError("Do not use the Expression version of the 'png' attribute.") 
        attr = getattr(self.expr, name)
        
        if hasattr(attr, '__call__') and 'assumptions' in inspect.getargspec(attr).args:
            # The attribute is a callable function with 'assumptions' as an argument.
            # Automatically include the KnownTruth assumptions.

            # note, index zero is self.
            assumptionsIndex = inspect.getargspec(attr).args.index('assumptions')-1
            
            def call_method_with_known_truth_assumptions(*args, **kwargs):
                if len(args) > assumptionsIndex:
                    args = list(args)
                    assumptions = args[assumptionsIndex]
                    assumptions = defaults.checkedAssumptions(assumptions)                    
                    assumptions += self.assumptions
                    args[assumptionsIndex] = defaults.checkedAssumptions(assumptions)
                else:
                    assumptions = kwargs.get('assumptions', USE_DEFAULTS)
                    assumptions = defaults.checkedAssumptions(assumptions)
                    assumptions = tuple(assumptions) + self.assumptions
                    kwargs['assumptions'] = defaults.checkedAssumptions(assumptions)
                return attr.__call__(*args, **kwargs)
            return call_method_with_known_truth_assumptions
        
        return attr
            
    
    def __dir__(self):
        '''
        The KnownTruth aquires the attributes of its Expression as well as its
        own attributes.
        '''
        return sorted(set(dir(self.__class__) + self.__dict__.keys() + dir(self.expr)))

    @staticmethod
    def findKnownTruth(expression, assumptionsSet):
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
            proof = truth.proof()
            if proof is not None and proof.isUsable() and truth.assumptionsSet.issubset(assumptionsSet):
                suitableTruths.append(truth)
        if len(suitableTruths)==0: return None # no suitable truth
        # return one wih the fewest assumptions, AND AMONG THOSE, WITH THE SHORTEST PROOF: TODO
        return min(suitableTruths, key=lambda truth : len(truth.assumptions))
    
    @staticmethod
    def forgetKnownTruths():
        KnownTruth.lookup_dict.clear()
    
    def _canSpecialize(self, var):
        '''
        Return True iff the given Variable can be specialized from
        this KnownTruth directly (an instance Variable of a directly
        nested Forall operation).
        '''
        from proveit.logic import Forall        
        expr = self.expr
        while isinstance(expr, Forall):
            if var in expr.instanceVars:
                return True
            expr = expr.instanceExpr
        return False      
        
    def relabel(self, relabelMap):
        '''
        Performs a relabeling derivation step, deriving another KnownTruth
        from this KnownTruth, under the same assumptions, with relabeled
        Variables.  A Variable may only be relabeled to a Variable.
        Returns the proven relabeled KnownTruth, or throws an exception if the proof fails.
        '''
        from proveit._core_.proof import Specialization
        return Specialization(self, numForallEliminations=0, relabelMap=relabelMap, assumptions=self.assumptions).provenTruth
    
    def specialize(self, specializeMap=None, relabelMap=None, assumptions=USE_DEFAULTS):
        '''
        Performs a specialize derivation step to be proven under the given
        assumptions, in addition to the assumptions of the KnownTruth.
        This will eliminate one or more nested Forall operations, specializing
        the instance variables according to specializeMap.  Eliminates
        the number of Forall operations required to utilize all of the
        specializeMap keys.  The default mapping of all instance variables
        is a mapping to itself (e.g., {x:x, y:y}).  Simultaneously, variables 
        may be relabeled via relabelMap (see the relabel method).  Note, there 
        is a difference between  making substitutons simultaneously versus 
        in-series.  For example, the {x:y, y:x} mapping will swap x and y 
        variables, but mapping {x:y} then {y:x} in series would set both 
        variables to x.
        Returns the proven specialized KnownTruth, or throws an exception if the
        proof fails.        
        '''
        from proveit import Operation, Variable, Lambda, singleOrCompositeExpression
        from proveit.logic import Forall
        from proof import Specialization, SpecializationFailure
        
        # if no specializeMap is provided, specialize a single Forall with default mappings (mapping instance variables to themselves)
        if specializeMap is None: specializeMap = dict()
        if relabelMap is None: relabelMap = dict()
                
        # Include the KnownTruth assumptions along with any provided assumptions
        assumptions = defaults.checkedAssumptions(assumptions)
        assumptions += self.assumptions

        # For any entrys in the subMap with Operation keys, convert
        # them to corresponding operator keys with Lambda substitutions.
        # For example f(x,y):g(x,y) would become f:[(x,y) -> g(x,y)].
        # Convert to composite expressions as needed (via singleOrCompositeExpression).
        processedSubMap = dict()
        for key, sub in specializeMap.iteritems():
            sub = singleOrCompositeExpression(sub)
            if isinstance(key, Operation):
                operation = key
                subVar = operation.operator
                sub = Lambda(operation.operands, sub)
                processedSubMap[subVar] = sub
            elif isinstance(key, Variable):
                processedSubMap[key] = sub
            else:
                raise SpecializationFailure(None, assumptions, 'Expecting specializeMap keys to be Variables, MultiVariables, or Operations with Variable/MultiVariable operators; not %s'%str(key.__class__))
        remainingSubVars = set(processedSubMap.keys())
        
        # Determine the number of Forall eliminations.  There must be at least
        # one (if zero is desired, relabel should be called instead).
        # The number is determined by the instance variables that occur as keys
        # in the subMap.
        expr = self.expr
        numForallEliminations = 0
        while numForallEliminations==0 or len(remainingSubVars) > 0:
            numForallEliminations += 1
            if not isinstance(expr, Forall):
                raise SpecializationFailure(None, assumptions, 'May only specialize instance variables of directly nested Forall operations')
            lambdaExpr = expr.operand
            assert isinstance(lambdaExpr, Lambda), "Forall Operation operand must be a Lambda function"
            instanceVars, expr, conditions  = lambdaExpr.parameterVars, lambdaExpr.body, lambdaExpr.conditions
            for iVar in instanceVars:
                if iVar in remainingSubVars:
                    # remove this instance variable from the remaining substitution variables
                    remainingSubVars.remove(iVar)
                elif iVar not in processedSubMap:
                    # default is to map instance variables to themselves
                    processedSubMap[iVar] = iVar

        return Specialization(self, numForallEliminations=numForallEliminations, specializeMap=processedSubMap, relabelMap=relabelMap, assumptions=assumptions).provenTruth
        
    def generalize(self, forallVarLists, domainLists=None, domain=None, conditions=tuple()):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized KnownTruth.  Can introduce any number of
        nested Forall operations to wrap the original statement,
        corresponding to the number of given forallVarLists and domains.
        A single variable list or single variable and a single domain may 
        be provided to introduce a single Forall wrapper.
        '''
        from proveit._core_.proof import Generalization
        from proveit import Variable, compositeExpression
        from proveit.logic import InSet
        
        if isinstance(forallVarLists, Variable):
            forallVarLists = [[forallVarLists]] # a single Variable to convert into a list of variable lists
        else:
            if not hasattr(forallVarLists, '__len__'):
                raise ValueError("Must supply 'generalize' with a Variable, list of Variables, or list of Variable lists.")
            if len(forallVarLists) == 0:
                raise ValueError("Must provide at least one Variable to generalize over")
            if all(isinstance(x, Variable) for x in forallVarLists):
                # convert a list of Variable/MultiVariables to a list of lists
                forallVarLists = [forallVarLists]
        
        # Add domain conditions as appropriate
        if domain is not None and domainLists is not None:
            raise ValueError("Either specify a 'domain' or a list of 'domainLists' but not both")
        if domain is not None:
            domainLists = [[domain]*len(forallVarList) for forallVarList in forallVarLists]
        if domainLists is not None:
            domainConditions = []
            for domainList, forallVarList in zip(domainLists, forallVarLists):
                domainList = compositeExpression(domainList)
                if len(domainList)==1:
                    domainList = [domainList[0]]*len(forallVarList)
                domainConditions += [InSet(instanceVar, domain) for instanceVar, domain in zip(forallVarList, domainList)]
            conditions = domainConditions + list(conditions)
        
        return Generalization(self, forallVarLists, conditions).provenTruth

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
    
    def evaluation(self):
        '''
        Calling evaluation on a KnownTruth results in deriving that its
        expression is equal to TRUE, under the assumptions of the KnownTruth.
        '''
        from proveit.logic import evaluateTruth
        return evaluateTruth(self.expr, self.assumptions)

    def asImpl(self, hypothesis):
        '''
        Abbreviation for asImplication.
        '''
        return self.asImplication(hypothesis)

    def raiseUnusableProof(self):
        from proof import UnusableProof, Theorem, Axiom
        proof = self.proof()
        unusuable_proof = proof._meaningData._unusableProof
        if proof == unusuable_proof:
            raise UnusableProof(KnownTruth.theoremBeingProven, unusuable_proof)        
        else:
            raise UnusableProof(KnownTruth.theoremBeingProven, unusuable_proof, 'required to prove' + self.string(performUsabilityCheck=False)) 

    def string(self, performUsabilityCheck=True):
        '''
        If the KnownTruth was proven under any assumptions, display the 
        double-turnstyle notation to show that the set of assumptions proves
        the statement/expression.  Otherwise, simply display the expression.
        '''
        from proveit import ExprList
        if performUsabilityCheck and not self.isUsable(): self.raiseUnusableProof()
        if len(self.assumptions) > 0:
            assumptionsStr = ExprList(*self.assumptions).formatted('string', fence=False)
            return r'{' +assumptionsStr + r'} |= ' + self.expr.string()
        return r'|= ' + self.expr.string()

    def __str__(self):
        '''
        Return a string representation of the KnownTruth.
        '''
        return self.string()
        
    def __repr__(self):
        '''
        Return a string representation of the KnownTruth.
        '''
        if not self.isUsable(): self.raiseUnusableProof()
        return self.string()
    
    def _repr_html_(self):
        '''
        Generate html to show the KnownTruth as a set of assumptions,
        turnstile, then the statement expression.  Expressions are png's
        compiled from the latex (that may be recalled from memory or storage 
        if previously generated) with a links to
        expr.ipynb notebooks for displaying the expression information.
        '''
        from proveit.logic import Set
        if not self.isUsable(): self.raiseUnusableProof()
        html = ''
        html += '<span style="font-size:20px;">'
        if len(self.assumptions) > 0:
            html += Set(*self.assumptions)._repr_html_()
        html += ' &#x22A2;&nbsp;' # turnstile symbol
        html += self.expr._repr_html_()
        html += '</span>'
        return html

def asExpression(truthOrExpression):
    '''
    Return the argument as Expressions.  That is, if the argument is the
    KnownTruth, yield its associated Expression.  If it is an Expression,
    yield just that.  Otherwise, raise a TypeError.
    '''
    if isinstance(truthOrExpression, KnownTruth):
        return truthOrExpression.expr
    elif isinstance(truthOrExpression, Expression):
        return truthOrExpression
    else:
        raise TypeError('Expected to be a KnownTruth or an Expression')
    
def asExpressions(*truthOrExpressions):
    '''
    Return the arguments as a list of Expressions via asExpression.
    '''
    return [asExpression(truthOrExpression) for truthOrExpression in truthOrExpression]

class ProofInitiationFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
