"""
A KnownTruth represents an expression that has been proven to be a true
statement.  A KnownTruth wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from storage import storage
from defaults import defaults, USE_DEFAULTS
import re
            
class KnownTruth:
    
    # lookup_dict maps Expressions to lists of KnownTruths for proving the 
    # Expression under various assumptions.  Excludes redundancies in which one set
    # of assumptions subsumes another.
    lookup_dict = dict()
    
    # Call the beginProof method to begin a proof of a Theorem.
    theoremBeingProven = None # Theorem being proven.
    dependentTheoremsOfTheoremBeingProven = None # set theorems that depend upon (directly or indirectly) the theorem be proven
    # Set of theorems/packages that are presumed to be True for the purposes of the proof being proven:
    presumingTheorems = None # set of Theorem objects when in use
    presumingPackages = None # set of package names or full theorem names when in use.

    # KnownTruths for which deriveSideEffects is in progress, tracked to prevent infinite
    # recursion when deducing side effects after something is proven.
    in_progress_to_derive_sideeffects = set() 


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
        self._proof = None # set this after the Proof does some initialization via _recordBestProof         
        # a unique representation for the KnownTruth comprises its expr and assumptions:
        self._unique_rep = self._generate_unique_rep(lambda expr : hex(expr._unique_id))
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)

    def _generate_unique_rep(self, objectRepFn):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        return objectRepFn(self.expr) + ';[' + ','.join(objectRepFn(assumption) for assumption in self.assumptions) + ']'

    @staticmethod
    def _referencedObjIds(unique_rep):
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
            self.expr.deriveSideEffects(self)
            KnownTruth.in_progress_to_derive_sideeffects.remove(self)        

    def __eq__(self, other):
        if isinstance(other, KnownTruth):
            return self._unique_id == other._unique_id
        else: return False # other must be an KnownTruth to be equal to self
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return self._unique_id
        
    def beginProof(self, presumes=tuple()):
        '''
        Begin a proof for a theorem.  Only use other theorems that are in 
        the presumes list of theorems/packages or have already been
        proven fully (down to the axioms) without depending upon this
        theorem.  If there exists any presumed theorem that has
        a direct or indirect dependence upon this theorem,
        then a CircularLogic exception is raised. 
        '''
        if KnownTruth.theoremBeingProven is not None:
            raise ProofInitiationFailure("May only beginProof once per Python/IPython session.  It is best to avoid having extraneous KnownTruth objects so each proof should be independent.")
        from proof import Theorem
        from proveit.certify import allDependents
        theorem = self.proof()
        if not isinstance(theorem, Theorem):
            raise TypeError('Only begin a proof for a Theorem')
        KnownTruth.theoremBeingProven = theorem
        KnownTruth.dependentTheoremsOfTheoremBeingProven = allDependents(theorem)
        KnownTruth.presumingTheorems = set()
        KnownTruth.presumingPackages = set()
        for presuming in presumes:
            if isinstance(presuming, KnownTruth):
                presuming = presuming.asTheoremOrAxiom()
            if isinstance(presuming, Theorem):
                KnownTruth.presumingTheorems.add(presuming)
            elif isinstance(presuming, str):
                # may be a package or a full theorem name, to be precise
                KnownTruth.presumingPackages.add(presuming)
            else:
                raise ValueError("'presumes' should be a collection of Theorems and strings, not " + str(presuming.__class__))
        Theorem.updateUsability()
        # check to see if the theorem was already proven before we started
        for proof in theorem._possibleProofs:
            if all(usedTheorem._unusableTheorem is None for usedTheorem in proof.usedTheorems()):
                print "Theorem already proven.  Calling qed() method."
                self._proof = proof
                return self.qed()
        print "Beginning proof of"
        return self.expr
    
    def qed(self):
        '''
        Complete a proof that began via `beginProof`, entering it into
        the certification database.
        '''
        from proveit.certify import recordProof
        if KnownTruth.theoremBeingProven is None:
            raise Exception('No theorem being proven; cannot call qed method')
        if self.expr != KnownTruth.theoremBeingProven.provenTruth.expr:
            raise Exception('qed does not match the theorem being proven')
        if len(self.assumptions) > 0:
            raise Exception('qed proof should not have any remaining assumptions')
        proof = self.expr.prove().proof()
        recordProof(KnownTruth.theoremBeingProven, proof)
        return proof

    def proof(self):
        '''
        Returns the most up-to-date proof of this KnownTruth.
        '''
        return self._proof
    
    def isUsable(self):
        '''
        Returns True iff this KnownTruth has a "usable" proof.  Proofs
        may be unusable when proving a theorem that is restricted with
        respect to which theorems may be used (to avoid circular logic).
        '''
        return self._proof is not None
    
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
        if isinstance(self._proof, Theorem) or isinstance(self._proof, Axiom):
            return self._proof
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
        from proof import Theorem
        if not newProof.isUsable():
            return # if it is not usable, forget it.
        if not self.expr in KnownTruth.lookup_dict:
            # the first KnownTruth for this Expression
            self._proof = newProof
            KnownTruth.lookup_dict[self.expr] = [self]
            return
        keptTruths = []
        bornObsolete = False
        for other in KnownTruth.lookup_dict[self.expr]:
            if other._proof is None or not other._proof.isUsable():
                # use the new proof since the old one is unusable.
                other._updateProof(self._proof)
            elif self.assumptionsSet == other.assumptionsSet:
                if newProof.numSteps <= other._proof.numSteps:
                    if newProof.requiredProofs != other._proof.requiredProofs:
                        # use the new (different) proof that does the job as well or better
                        if isinstance(newProof, Theorem):
                            # newer proof is a theorem; record the existing proof as a possible proof for that theorem
                            newProof._possibleProofs.append(other._proof)
                        other._updateProof(newProof)
                else:
                    # the new proof was born obsolete, taking more steps than an existing one
                    if isinstance(other._proof, Theorem):
                        # the older proof is a theorem, recode the new proof as a possible proof for that theorem
                        other._proof._possibleProofs.append(newProof)
                    self._proof = other._proof # use an old proof that does the job better
                    keptTruths.append(other)
                    bornObsolete = True
            elif self.assumptionsSet.issubset(other.assumptionsSet):
                # use the new proof that does the job better
                other._updateProof(self._proof) 
            elif self.assumptionsSet.issuperset(other.assumptionsSet):
                # the new proof was born obsolete, requiring more assumptions than an existing one
                self._proof = other._proof # use an old proof that does the job better
                keptTruths.append(other)
                bornObsolete = True
            else:
                # 'other' uses a different, non-redundant set of assumptions
                keptTruths.append(other)
        if not bornObsolete:
            self._proof = newProof
            keptTruths.append(self)
        # Remove the obsolete KnownTruths from the lookup_dict
        KnownTruth.lookup_dict[self.expr] = keptTruths

    def _updateProof(self, newProof):
        '''
        Update the proof of this KnownTruth which has been made obsolete.
        Dependents of the old proof must also be updated.  If newProof
        is None, the proof and its dependents are eliminated from memory.
        '''
        oldDependents = [] if self._proof is None else self._proof.updatedDependents()
        self._proof = newProof # set to the new proof
        for oldDependentProof in oldDependents:
            if newProof is None:
                # eliminating this proof and its dependents from memory 
                oldDependentProof.provenTruth._updateProof(None)
            else:                
                # remake the dependent proof to refer to this updated proof
                oldDependentProof.remake()

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
            if truth._proof is not None and truth.assumptionsSet.issubset(assumptionsSet):
                suitableTruths.append(truth)
        if len(suitableTruths)==0: return None # no suitable truth
        # return one wih the fewest assumptions
        return min(suitableTruths, key=lambda truth : len(truth.assumptions))
    
    @staticmethod
    def forgetKnownTruths():
        KnownTruth.lookup_dict.clear()

    def relabel(self, relabelMap):
        '''
        Performs a relabeling derivation step, deriving another KnownTruth
        from this KnownTruth, under the same assumptions, with relabeled
        Variables/MultiVariables.  A Variable may only be relabeled to a Variable.
        A MultiVariable may be relabeled to a Composite Expression (ExpressionList,
        ExpressionTensor, or NamedExpressions as appropriate) of Variables/MultiVariables)
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
        from proveit import Operation, Variable, MultiVariable, Composite, compositeExpression, ExpressionList, ExpressionTensor, Lambda
        from proveit import Forall
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
        # For MultiVariable operators, there will be composite substitutions.
        processedSubMap = dict()
        for key, sub in specializeMap.iteritems():
            if isinstance(key, Operation):
                operation = key
                subVar = operation.operator
                if isinstance(key.operator, MultiVariable):
                    lambdaExpressions = compositeExpression(sub)
                    if lambdaExpressions.__class__ == ExpressionList:
                        sub = ExpressionList([Lambda(operation.operands, lambdaExpr) for lambdaExpr in lambdaExpressions])
                    elif lambdaExpressions.__class__ == ExpressionTensor:
                        sub = ExpressionTensor({tensorKey:Lambda(operation.operands, lambdaExpr) for tensorKey, lambdaExpr in lambdaExpressions.iteritems()}, shape=lambdaExpressions.shape, alignmentCoordinates=lambdaExpressions.alignmentCoordinates)
                else:
                    if not isinstance(sub, Expression) or isinstance(sub, Composite):
                        raise SpecializationFailure(None, assumptions, 'Only MultiVariable operations may be be specialized to a composite Expression')
                    sub = Lambda(operation.operands, sub)
                processedSubMap[subVar] = sub
            elif isinstance(key, MultiVariable):
                processedSubMap[key] = compositeExpression(sub) # MultiVariables map to a Composite
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
            expr = expr.operands
            lambdaExpr = expr['instance_mapping'];
            assert isinstance(lambdaExpr, Lambda), "Forall Operation lambdaExpr must be a Lambda function"
            instanceVars, expr, conditions  = lambdaExpr.parameters, lambdaExpr.body['instance_expression'], lambdaExpr.body['conditions']
            for iVar in instanceVars:
                if iVar in remainingSubVars:
                    # remove this instance variable from the remaining substitution variables
                    remainingSubVars.remove(iVar)
                elif iVar not in processedSubMap:
                    # default is to map instance variables to themselves
                    processedSubMap[iVar] = iVar

        # Make sure MultiVariables are relabeled to composite expressions, as a consistent convention
        relabelMap = {key : compositeExpression(sub) if isinstance(key, MultiVariable) else sub for key, sub in relabelMap.iteritems()}
        
        return Specialization(self, numForallEliminations=numForallEliminations, specializeMap=processedSubMap, relabelMap=relabelMap, assumptions=assumptions).provenTruth
        
    def generalize(self, forallVarLists, domains=None, domain=None, conditions=tuple()):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized KnownTruth.  Can introduce any number of
        nested Forall operations to wrap the original statement,
        corresponding to the number of given forallVarLists and domains.
        A single variable list or single variable and a single domain may 
        be provided to introduce a single Forall wrapper.
        '''
        from proveit._core_.proof import Generalization
        from proveit import Variable
        if isinstance(forallVarLists, Variable):
            forallVarLists = [[forallVarLists]] # a single Variable to convert into a list of variable lists
        else:
            for forallVarListsElem in forallVarLists:
                if isinstance(forallVarListsElem, Variable):
                    # must be a single list, so let's convert it to a list of lists
                    forallVarLists = [forallVarLists]
        if domain is not None and domains is not None:
            raise ValueError("Either specify a 'domain' or a list of 'domains' but not both")
        if domains is None:
            domains = [domain]*len(forallVarLists)
        return Generalization(self, forallVarLists, domains, conditions).provenTruth

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
    
    def evaluate(self):
        '''
        Calling evaluate on a KnownTruth results in deriving that its
        expression is equal to TRUE, under the assumptions of the KnownTruth.
        '''
        from proveit import evaluateTruth
        return evaluateTruth(self.expr, self.assumptions)

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
        if not self.isUsable():
            raise Exception('KnownTruth unusable in this proof')
        if len(self.assumptions) > 0:
            return r'\{' + ','.join(assumption.latex() for assumption in self.assumptions) + r'\} \boldsymbol{\vdash} ' + self.expr.latex()
        return r'\boldsymbol{\vdash} ' + self.expr.latex()

    def string(self):
        '''
        If the KnownTruth was proven under any assumptions, display the 
        double-turnstyle notation to show that the set of assumptions proves
        the statement/expression.  Otherwise, simply display the expression.
        '''
        if not self.isUsable():
            raise Exception('KnownTruth unusable in this proof')
        if len(self.assumptions) > 0:
            return r'{' + ','.join(assumption.string() for assumption in self.assumptions) + r'} |= ' + self.expr.string()
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
        if not self.isUsable():
            raise Exception('KnownTruth unusable in this proof')
        return self.string()
    
    def _storage(self):
        '''
        If the KnownTruth is for an Axiom or Theorem, use the _certified_
        storage for the package.  Otherwise use the default storage.
        '''
        from proveit.certify import _makeStorage
        from proof import Axiom, Theorem
        if self._proof is not None and (isinstance(self._proof, Axiom) or isinstance(self._proof, Theorem)):
            return _makeStorage(self._proof.package)
        return storage

    def _repr_png_(self):
        '''
        Generate a png image from the latex.  May be recalled from memory or
        storage if it was generated previously.
        '''
        if not self.isUsable():
            raise Exception('KnownTruth unusable in this proof')
        if not hasattr(self,'png'):
            self.png = self._storage()._retrieve_png(self, self.latex(), self._config_latex_tool)
        return self.png # previous stored or generated

    def generate_html(self):
        '''
        Generate the img html tag with encoded png data.
        '''
        self._repr_png_() # sets self.png
        import base64
        return '<img src="data:image/png;base64,' + base64.b64encode(self.png) + '">'        
        
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
        for assumption in self.assumptions:
            assumption._config_latex_tool(lt)

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
