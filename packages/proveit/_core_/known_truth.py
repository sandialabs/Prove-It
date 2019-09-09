"""
A KnownTruth represents an expression that has been proven to be a true
statement.  A KnownTruth wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from proveit._core_._unique_data import meaningData, styleData
from .defaults import defaults, USE_DEFAULTS
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
        from .proof import Proof
        assert isinstance(newproof, Proof)
        assert newproof.provenTruth.expr == self._expr
        self._proofs.add(newproof)
    
    def discard(self, oldproof):
        from .proof import Proof
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
    # lookup_dict maps each Expression to a set of KnownTruths for proving the 
    # Expression under various assumptions.
    lookup_dict = dict()
    
    # (KnownTruth, default assumptions) pairs for which deriveSideEffects has been called.  
    # We track this to make sure we didn't miss anything while automation was disabled and then re-enabled.
    sideeffect_processed = set()
    
    # Call the beginProof method to begin a proof of a Theorem.
    theoremBeingProven = None # Theorem being proven.
    hasBeenProven = None # Has the theoremBeingProven been proven yet in this session?  
                         # Goes from None to False (after beginning a proof and disabling Theorems that cannot be used)
                         # to True (when there is a legitimate proof).
    # Set of theorems/packages that are presumed to be True for the purposes of the proof being proven:
    presumingTheoremNamess = None # set of full names of presumed theorems when in use
    presumingPrefixes = None # set of context names or full theorem names when in use.
    qedInProgress = False # set to true when "%qed" is in progress

    # KnownTruths for which deriveSideEffects is in progress, tracked to prevent infinite
    # recursion when deducing side effects after something is proven.
    in_progress_to_derive_sideeffects = set() 

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the KnownTruth jurisdiction.
        '''
        KnownTruth.lookup_dict.clear()
        KnownTruth.sideeffect_processed.clear()
        KnownTruth.theoremBeingProven = None
        KnownTruth.hasBeenProven = None
        KnownTruth.presumingTheorems = None
        KnownTruth.presumingPrefixes = None
        KnownTruth.qedInProgress = False
        _ExprProofs.all_expr_proofs.clear()
        assert len(KnownTruth.in_progress_to_derive_sideeffects)==0, "Unexpected remnant 'in_progress_to_derive_sideeffects' items (should have been temporary)"

    def __init__(self, expression, assumptions):
        '''
        Create a KnownTruth with the given Expression, set of assumptions.  These
        should not be created manually but rather through the creation of Proofs which should
        be done indirectly via Expression/KnownTruth derivation-step methods.
        '''
        from proveit._core_.proof import Proof
        # print("Begin Initializing KnownTruth!")                                 # for testing; delete later
        # do some type checking
        if not isinstance(expression, Expression):
            raise ValueError('The expression (expr) of a KnownTruth should be an Expression')
        for assumption in assumptions:
            if not isinstance(assumption, Expression):
                raise ValueError('Each assumption should be an Expression')

        # print("    After type-checking, expression = ", expression)             # for testing; delete later
        
        # note: these contained expressions are subject to style changes on a KnownTruth instance basis
        self.expr = expression
        # store the assumptions as an ordered list (with the desired
        # order for display) and an unordered set (for convenience when
        # checking whether one set subsumes another).
        self.assumptions = tuple(assumptions)
        self.assumptionsSet = frozenset(assumptions)
        # print("    assumptions = ", assumptions)                                # for testing; delete later

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

        # print("    Exiting KnownTruth.__init__")                                # for testing; delete later
        
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
                
    def deriveSideEffects(self, assumptions):
        '''
        Derive any side-effects that are obvious consequences arising from this truth.
        Called after the corresponding Proof is complete.
        '''
        from .proof import ProofFailure
        if not defaults.automation:
            return # automation disabled
        # Sort the assumptions according to hash key so that sets of assumptions
        # are unique for determining which side-effects have been processed already.
        sorted_assumptions = tuple(sorted(assumptions, key=lambda expr : hash(expr)))
        if (self.expr, sorted_assumptions) in KnownTruth.sideeffect_processed:
            return # has already been processed
        if self not in KnownTruth.in_progress_to_derive_sideeffects:
            # avoid infinite recursion by using in_progress_to_deduce_sideeffects
            KnownTruth.in_progress_to_derive_sideeffects.add(self)
            try:
                for sideEffect in self.expr.sideEffects(self):
                    # Attempt each side-effect derivation, specific to the
                    # type of Expression.
                    try:
                        # use the default assumptions which are temporarily set to the
                        # assumptions utilized in the last derivation step.
                        sideEffect(assumptions=assumptions)     
                    except ProofFailure:
                        pass
                    except Exception as e:
                        raise Exception("Side effect failure for %s, while running %s: "%(str(self.expr), str(sideEffect)) + str(e))
            finally:
                KnownTruth.in_progress_to_derive_sideeffects.remove(self)        
            KnownTruth.sideeffect_processed.add((self.expr, sorted_assumptions))

    def __eq__(self, other):
        if isinstance(other, KnownTruth):
            return self._meaning_id == other._meaning_id
        else: return False # other must be an Expression to be equal to self
    
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id
        
    def beginProof(self, theorem, presuming=tuple(), justRecordPresumingInfo=False):
        '''
        Begin a proof for a theorem.  Only use other theorems that are in 
        the presuming list of theorems/packages or theorems that are required,
        directly or indirectly, in proofs of theorems that are explicitly 
        listed (these are implicitly presumed).  If there exists any 
        presumed theorem that has a direct or indirect dependence upon this 
        theorem then a CircularLogic exception is raised. 
        '''
        from .context import Context, ContextException
        from .proof import Theorem
        if KnownTruth.theoremBeingProven is not None:
            raise ProofInitiationFailure("May only beginProof once per Python/IPython session.  Restart the notebook to restart the proof.")
        if not isinstance(theorem, Theorem):
            raise TypeError('Only begin a proof for a Theorem')
        if theorem.provenTruth != self:
            raise ValueError('Inconsistent theorem for the KnownTruth in beginProof call')
                
        # Note: all previous theorems of the context are presumed automatically.
        context = theorem.context
        num_prev_thms = 0 # number of previous theorems within the context
        for prev_thm_name in context.theoremNames():
            if prev_thm_name == theorem.name:
                break # concludes all "previous" theorems of the context
            if (context.name + '.' +  prev_thm_name) in presuming:
                raise ValueError("Do not explicitly presuming any previous theorems of the context.  They are automatically presumed.")
            num_prev_thms += 1
        
        # split the presuming information into specific theorems (which are transitively presumed)
        # and entire contexts (which are not transitively presumed only applies to theorems of
        # the other context that do not presume this one).
        explicitly_presumed_thm_names = [] # list of theorem name strings
        presumed_context_names = [] # list of context name strings
        for presumption_name in presuming:
            if '.' in presumption_name:
                try:
                    context_name, theorem_name = presumption_name.rsplit('.', 1)
                    context = Context.getContext(context_name)
                    # Ensure we load the theorem and derive its automatic side-effects
                    # for these explicitly presumed theorems (but not the indirectly
                    # presumed ones).
                    context.getTheorem(theorem_name)
                    # it is a theorem
                    explicitly_presumed_thm_names.append(presumption_name) # append as a string
                    continue # continue to the next thing
                except (ContextException, KeyError):
                    pass
            # it must not be a theorem; it should be a Context.
            presumed_context_names.append(presumption_name) # not a theorem; must be a context
        
        # record the explicitly presumed theorems
        theorem.recordPresumedContexts(sorted(presumed_context_names))
        theorem.recordPresumedTheorems(sorted(explicitly_presumed_thm_names))
        if justRecordPresumingInfo: return self.expr
        print("Recorded 'presuming' information")
        
        # The full list of presumed theorems includes all previous theorems
        # of the context and all indirectly presumed theorems via transitivity
        # (a presumption of a presumption is a presumption).
        presumed_theorem_names = theorem.getAllPresumedTheoremNames()

        if str(self) in presumed_theorem_names:
            from .proof import CircularLogic
            # extra sanity check (should be caught within getAllPresumedTheoremNames)
            raise CircularLogic(theorem, theorem)
        
        KnownTruth.theoremBeingProven = theorem
        KnownTruth.presumingTheoremNames = set(presumed_theorem_names)
        KnownTruth.presumingPrefixes = set(presumed_context_names)
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
        if len(presumed_context_names) > 0:
            print("Presuming theorems in %s (except any that presume this theorem)."%', '.join(sorted(presumed_context_names)))
        if len(explicitly_presumed_thm_names) > 0:
            theorem_or_theorems = 'theorem' if len(explicitly_presumed_thm_names)==1 else 'theorems'
            print("Presuming %s %s (applied transitively)."%(', '.join(sorted(str(thm) for thm in explicitly_presumed_thm_names)), theorem_or_theorems))
        if num_prev_thms > 0:
            theorem_or_theorems = 'theorem' if num_prev_thms==1 else 'theorems'
            print("Presuming previous %s (applied transitively)."%theorem_or_theorems)
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
        try:
            proof = self.expr.prove().proof()
            if not proof.isUsable():
                proof.provenTruth.raiseUnusableProof()
            KnownTruth.theoremBeingProven.recordProof(proof)
        finally:
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
        from .proof import Theorem, Axiom
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
            print(axiom)
        if len(requiredTheorems) == 0:
            assert isFullyProven(self), "certification database is corrupt"
            print("Theorem is fully proven!")
        if len(requiredTheorems) > 0:
            assert not isFullyProven(self), "certification database is corrupt"
            print("\nUnproven theorems:")
            for theorem in sorted(requiredTheorems):
                print(theorem)

    def printDependents(self):
        '''
        Provided that this KnownTruth is known to represent a theorem or axiom,
        print all theorems that are known to depend on it directly or indirectly.
        '''
        from proveit.certify import allDependents
        dependents = allDependents(self)
        for theorem in sorted(dependents):
            print(theorem)
    
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
        expr_known_truths = KnownTruth.lookup_dict.setdefault(self.expr, set())
        expr_known_truths.add(self)
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
                        print('%s has been proven. '%self.asTheoremOrAxiom().name, r'Now simply execute "%qed".')
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
        return sorted(set(dir(self.__class__) + list(self.__dict__.keys()) + dir(self.expr)))

    def withMatchingStyles(self, expr, assumptions):
        '''
        Alter the styles of the KnownTruth expression and any of its assumptions
        to match the given styles.
        '''
        self.expr.withMatchingStyle(expr)
        # storing the assumptions in a trivial dictionary will be useful for popping them out.
        assumptions_dict = {assumption:assumption for assumption in assumptions}
        for assumption in self.assumptions:
            if assumption in assumptions_dict:
                assumption.withMatchingStyle(assumptions_dict.pop(assumption))
        proof = self.proof()
        if proof is not None:
            if proof.provenTruth._style_id != self._style_id:
                proof.provenTruth.withMatchingStyles(expr, assumptions)
        return self
    
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
        # return one wih the shortest proof, and among those the fewest assumptions
        return min(suitableTruths, key=lambda truth : (truth.proof().numSteps(), len(truth.assumptions)))
    
    @staticmethod
    def forgetKnownTruths():
        '''
        Forget all KnownTruth's and all Assumption proof objects.  This is used
        for demonstration purposes in the tutorial, but should not generally be needed.
        '''
        from proof import Assumption
        KnownTruth.lookup_dict.clear()
        Assumption.allAssumptions.clear()
    
    def _checkedTruth(self, proof):
        proven_truth = proof.provenTruth
        if not proven_truth.isUsable():
            proven_truth.raiseUnusableProof()
        return proven_truth        
        
    def relabel(self, relabelMap):
        '''
        Performs a relabeling derivation step, deriving another KnownTruth
        from this KnownTruth, under the same assumptions, with relabeled
        Variables.  A Variable may only be relabeled to a Variable.
        Returns the proven relabeled KnownTruth, or throws an exception if the proof fails.
        '''
        from proveit._core_.proof import Specialization
        return self._checkedTruth(Specialization(self, numForallEliminations=0, relabelMap=relabelMap, assumptions=self.assumptions))
        
    def specialize(self, specializeMap=None, relabelMap=None, assumptions=USE_DEFAULTS):
        '''
        Performs a specialize derivation step to be proven under the
        given assumptions, in addition to the assumptions of the
        KnownTruth. This will eliminate one or more nested Forall
        operations, specializing the instance variables according to
        specializeMap.  Eliminates the number of Forall operations
        required to utilize all of the specializeMap keys.  The default
        mapping of all instance variables is a mapping to itself
        (e.g., {x:x, y:y}).  Simultaneously, variables may be relabeled
        via relabelMap (see the relabel method).  Note, there is a
        difference between  making substitutons simultaneously versus
        in-series.  For example, the {x:y, y:x} mapping will swap x and
        y variables, but mapping {x:y} then {y:x} in series would set
        both variables to x.
        Returns the proven specialized KnownTruth, or throws an
        exception if the proof fails.        
        '''
        from proveit import (
                Lambda,
                Operation,
                singleOrCompositeExpression,
                Variable)
        from proveit.logic import Forall
        from .proof import (
                ProofFailure,
                Specialization,
                SpecializationFailure)
        
        if not self.isUsable():
            # If this KnownTruth is not usable (i.e. its use has been
            # restricted) see if there is an alternate under the set
            # of assumptions that is usable.
            try:
                alternate = self.expr.prove(assumptions, automation=False)
            except ProofFailure:
                self.raiseUnusableProof()
            return alternate.specialize(specializeMap,
                                        relabelMap,
                                        assumptions)
        
        # if no specializeMap is provided, specialize the
        # "explicitInstanceVars" of the Forall with default mappings 
        # (mapping instance variables to themselves)
        if specializeMap is None:
            specializeMap = {ivar:ivar for ivar in self.explicitInstanceVars()}
        if relabelMap is None: relabelMap = dict()
                
        # Include the KnownTruth assumptions along with any provided assumptions
        assumptions = defaults.checkedAssumptions(assumptions)
        assumptions += self.assumptions

        # For any entries in the subMap with Operation keys, convert
        # them to corresponding operator keys with Lambda substitutions.
        # For example f(x,y):g(x,y) would become f:[(x,y) -> g(x,y)].
        # Convert to composite expressions as needed
        # (via singleOrCompositeExpression).
        processedSubMap = dict()
        for key, sub in specializeMap.items():
            sub = singleOrCompositeExpression(sub)
            if isinstance(key, Operation):
                operation = key
                subVar = operation.operator
                sub = Lambda(operation.operands, sub)
                processedSubMap[subVar] = sub
            elif isinstance(key, Variable):
                processedSubMap[key] = sub
            else:
                raise SpecializationFailure(
                        None, assumptions,
                        ('Expecting specializeMap keys to be ' +
                         'Variables, MultiVariables, or Operations ' +
                         'with Variable/MultiVariable operators; not ' +
                         ' %s'%str(key.__class__))
                )
        remainingSubVars = set(processedSubMap.keys())
        
        # Determine the number of Forall eliminations.  There must be
        # at least one (if zero is desired, relabel should be called
        # instead). The number is determined by the instance variables
        # that occur as keys in the subMap.
        expr = self.expr
        numForallEliminations = 0
        while numForallEliminations==0 or len(remainingSubVars) > 0:
            numForallEliminations += 1
            if not isinstance(expr, Forall):
                raise SpecializationFailure(
                        None, assumptions,
                        ('May only specialize instance variables of ' +
                        ' directly nested Forall operations')
                )
            lambdaExpr = expr.operand
            assert isinstance(lambdaExpr, Lambda), (
                "Forall Operation operand must be a Lambda function")
            instanceVars, expr, conditions  = lambdaExpr.parameterVars, lambdaExpr.body, lambdaExpr.conditions
            for iVar in instanceVars:
                if iVar in remainingSubVars:
                    # remove this instance variable from the remaining
                    # substitution variables
                    remainingSubVars.remove(iVar)
                elif iVar not in processedSubMap:
                    # default is to map instance variables to themselves
                    processedSubMap[iVar] = iVar

        return self._checkedTruth(
                Specialization(
                        self,
                        numForallEliminations=numForallEliminations,
                        specializeMap=processedSubMap,
                        relabelMap=relabelMap,
                        assumptions=assumptions)
                )


    # Introduced by wdc starting Tues 7/30/2019
    # May need to restrict Skolem constants from being utilized in
    # the specialize() method!
    def skolemize( self, skolemizeMap=None, relabelMap=None,
                   assumptions=USE_DEFAULTS):
        '''
        Performs a skolemization derivation step or possibly multiple
        skolemization steps, based on the user-provided skolemizeMap
        specifying a Literal to be substituted for each desired
        Exists instance variable.
        to be proven under the
        given assumptions, in addition to the assumptions of the
        KnownTruth. This will eliminate one or more nested Exists
        operations, skolemizing the Exists instance variables according
        to specializeMap.  Eliminates the number of Exists operations
        required to utilize all of the skolemizeMap keys. There is no
        default skolemizeMap implemented -- if a skolemize map is not
        provided, then the method returns an error.  Simultaneously,
        variables may be relabeled via relabelMap (see the relabel
        method).  Note, there is a difference between  making 
        substitutons simultaneously versus in-series. For example, the
        {x:y, y:x} mapping will swap x and y variables, but mapping
        {x:y} then {y:x} in series would set both variables to x.
        Returns the proven skolemized KnownTruth, or throws an
        exception if the proof fails.        
        '''

        print("ENTERING KT.skolemize()")                                        # for testing; delete later
        
        from proveit import (
            Function, Lambda, Literal, Operation,
            singleOrCompositeExpression, Variable 
        )
        from proveit.logic import Exists, Forall
        from .proof import (
            ProofFailure, Skolemization, SkolemizationFailure,
            Specialization, SpecializationFailure
        )

        # will be able to delete a few of those imports
        # a little later — probably the Forall and Specialization-
        # related stuff.
        
        # If no skolemizeMap is provided, raise a SkolemizationFailure
        # error message. Notice that this is different from the
        # specialize() method, which provides for a default
        # specializeMap. We might reconsider this later.
        if skolemizeMap is None:
            raise SkolemizationFailure(
                None,
                assumptions,
                ('skolemizeMap appears to be NONE. Expecting ' + 
                 'a skolemizeMap to specify the Variable-to-Literal ' + 
                 'mapping details.')
            )
        if relabelMap is None: relabelMap = dict()


        # Include the KnownTruth assumptions along with any provided
        # assumptions.
        # Why do we want to include the KnownTruth assumptions?
        # Notice that those are also the assumptions we would want
        # to include in the eventual KnownTruths derived by
        # skolemization -- i.e. if the initial KT was
        # A |– Exists(x, P(x)), then we would want the derived KT
        # A |- P(c) for Skolem constant 'c'
        assumptions = defaults.checkedAssumptions(assumptions)
        assumptions += self.assumptions


        if not self.isUsable():
            # If this KnownTruth is not usable (i.e. we have somehow
            # restricted its use to avoid circular reasoning, etc),
            # see if there is an alternate under the set of assumptions
            # that is usable.
            try:
                alternate = self.expr.prove(assumptions,
                                            automation=False)
            except ProofFailure:
                self.raiseUnusableProof()
            return alternate.specialize(specializeMap,
                                        relabelMap,
                                        assumptions)
        
        
        # The following mimics a similar block of code in the
        # specialize() method above.
        # For any entries in the skolemizeMap with Operation keys,
        # convert them to corresponding operator keys with Lambda
        # substitutions. For example f(x,y):g(x,y) would become
        # f:[(x,y) -> g(x,y)]. Convert to composite expressions as
        # needed (via singleOrCompositeExpression). Provide error
        # message if any skolemizeMap keys are NOT Variables,
        # Multivariables, or Operations with Variable/MultiVariable
        # operators.

        processedSubMap = dict()
        for key, sub in skolemizeMap.items():
            sub = singleOrCompositeExpression(sub)
            if isinstance(key, Operation): # haven't looked at ANY such possibilities yet
                operation = key
                subVar = operation.operator
                sub = Lambda(operation.operands, sub)
                processedSubMap[subVar] = sub
            elif isinstance(key, Variable): # only looking at these possibilities right now
                # proceed as normal, keeping the original
                # key:sub values
                processedSubMap[key] = sub
            else:
                raise SkolemizationFailure(
                    None,
                    assumptions,
                    ('Expecting skolemizeMap keys to be Variables, ' +
                     'MultiVariables, or Operations with ' +
                     'Variable/MultiVariable operators; ' +
                     'but "%s" is %s'%(key, str(key.__class__)))
                )
            print("        processedSubMap so far = ", processedSubMap)         # for testing; delete later
        # collect the remaining variables to be substituted for
        remainingSubVars = set(processedSubMap.keys())


        # Determine the number of Exists eliminations.
        # There must be at least one. If zero is desired, then relabel
        # should be called instead. The number is determined by the
        # instance variables that occur as keys in the skolemizeMap.
        expr = self.expr

        numExistsEliminations = 0
        while numExistsEliminations==0 or len(remainingSubVars) > 0:
            # we increase the number of Exists eliminations AND
            # decrease the number of items in the remainingSubVars list
            # so this process stops when we run out of the remainingSubVars
            # which is the list of variables to be skolemized
            numExistsEliminations += 1
            if not isinstance(expr, Exists):
                raise SkolemizationFailure(
                        None, assumptions,
                        'May only skolemize an Exists expression.')
            lambdaExpr = expr.operand
            assert isinstance(lambdaExpr, Lambda), (
                "Exists Operation operand must be a Lambda function")
            instanceVars, expr, conditions  = (lambdaExpr.parameterVars,
                                               lambdaExpr.body,
                                               lambdaExpr.conditions)



            for iVar in instanceVars:
                if iVar in remainingSubVars:
                    # remove this instance variable from the remaining
                    # substitution variables; this instance variable
                    # should already be in the processedSubMap
                    remainingSubVars.remove(iVar)
                elif iVar not in processedSubMap:
                    # default is to map instance variables to themselves
                    # BUT WE DO NOT WANT TO DEFAULT MAP ANYTHING FOR
                    # SKOLEMIZATION :(
                    # processedSubMap[iVar] = iVar
                    print("KT.skolemize() Hah! iVar not in " +
                          "processedSubMap")


        # Verify that all requested substitution values are actually
        # Literals or Literal operators for a Function and not
        # previously used to skolemize, or previously constrained in
        # an Axiom or Theorem, and verify that such
        # requested substitution values do not appear more than once.
        # If a substitution value is not a Literal or Literal operator,
        # or if a substitution value has already been marked as having
        # been used as a Skolem constant, or if a substitution value
        # appears more than once in the skolemizeMap, raise a
        # SkolemizationFailure error message.
        # NOTE: Should we also be checking for CONSTRAINED Literals
        # here as well (i.e. Literals that have already appeared in
        # an Axiom or Theorem)?
        tempSetOfIntendedSkolemSubs = set()
        for key, sub in skolemizeMap.items():
            sub = singleOrCompositeExpression(sub) # might not need this?
            # check if sub is actually a function rather than
            # just a simple constant, then focus on the operator itself
            # for example, if sub = f(x), then just grab the f
            if isinstance(sub, Function):
                sub = sub.operator
            print('sub is currently: ', sub)                                    # for testing; delete later
            if not isinstance(sub, Literal):
                raise SkolemizationFailure(
                        None,
                        assumptions,
                        ('Expecting skolemizeMap substitution values ' +
                         'to be Literals, but "%s" is %s'%(
                            sub, str(key.__class__))
                        )
                )
            if isinstance(sub, Literal) and sub.isSkolemConstant():
                raise SkolemizationFailure(
                        None,
                        assumptions,
                        ('Expecting skolemizeMap substitution ' +
                         'values to be Literals not previously ' +
                         'used to skolemize. "%s" was found to have ' +
                         'been marked as having already been used ' +
                         'elsewhere to skolemize.')%sub
                )
            if isinstance(sub, Literal) and sub.isConstrained():
                raise SkolemizationFailure(
                        None,
                        assumptions,
                        ('Expecting skolemizeMap substitution ' +
                         'values to be Literals not previously ' +
                         'constrained. "%s" was found to have ' +
                         'been previously constrained elsewhere ' +
                         '(perhaps in an Axiom or Theorem).')%sub
                )
            if sub in tempSetOfIntendedSkolemSubs:
                raise SkolemizationFailure(
                        None,
                        assumptions,
                        ('Expecting skolemizeMap substitution ' +
                         'values to be unique. "%s" was found to ' +
                         'appear multiple times as a requested ' +
                         'skolemization value.')%sub
                )
            else:
                tempSetOfIntendedSkolemSubs.add(sub)

        checkedTruths = KnownTruths(
            [self._checkedTruth(truth) for truth in Skolemization._makeSkolemizations(
                self,
                numExistsEliminations=numExistsEliminations,
                skolemizeMap=processedSubMap,
                relabelMap=relabelMap,
                assumptions=assumptions)]
            )

        # Multiple proofs may be generated when skolemizing an
        # expression that includes conditions, so take some care
        # about what we're returning
        if len(checkedTruths)==1:
            return checkedTruths[0]
        return checkedTruths

        
        
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
        
        return self._checkedTruth(Generalization(self, forallVarLists, conditions))

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
        return self._checkedTruth(HypotheticalReasoning(self, hypothesis))
        
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
        from .proof import UnusableProof, Theorem, Axiom
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
            return r'{' +assumptionsStr + r'} |- ' + self.expr.string()
        return r'|- ' + self.expr.string()

    def latex(self, performUsabilityCheck=True):
        '''
        If the KnownTruth was proven under any assumptions, display the 
        double-turnstyle notation to show that the set of assumptions proves
        the statement/expression.  Otherwise, simply display the expression.
        '''
        from proveit import ExprList
        if performUsabilityCheck and not self.isUsable(): self.raiseUnusableProof()
        if len(self.assumptions) > 0:
            assumptionsLatex = ExprList(*self.assumptions).formatted('latex', fence=False)
            return r'{' +assumptionsLatex + r'} \vdash ' + self.expr.latex()
        return r'\vdash ' + self.expr.string()

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

class KnownTruths(list):
    '''
    A list of KnownTruths, the class defined to help provide a way
    to print/output a list of KnownTruths returned by something like
    the skolemize() or specialize() KnownTruth methods.
    '''

    def _repr_html_(self):
        return "; ".join(kt._repr_html_() for kt in self)

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
