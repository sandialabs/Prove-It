"""
This is the expression module.
"""

from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.storage import storage

class Expression:
    unique_id_map = dict() # map unique_id's to unique_rep's
    expr_to_prove = None # the theorem currently being proven (if there is one)
    
    def __init__(self, coreInfo, subExpressions=tuple()):
        '''
        Initialize an expression with the given coreInfo (information relevant at the core Expression-type
        level) which should be a list (or tuple) of strings, and a list (or tuple) of subExpressions.
        '''
        for coreInfoElem in coreInfo:
            if not isinstance(coreInfoElem, str):
                raise TypeError('Expecting coreInfo elements to be of string type')
        for subExpression in subExpressions:
            if not isinstance(subExpression, Expression):
                raise TypeError('Expecting subExpression elements to be of Expression type')
        # unique_rep is a unique representation based upon the coreInfo and unique_id's of sub-Expressions
        self._coreInfo, self._subExpressions = coreInfo, subExpressions
        self._unique_rep = str(self.__class__) + '[' + ','.join(self._coreInfo) + '];[' + ','.join(hex(expr._unique_id) for expr in subExpressions) + ']'
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)
        while self._unique_id in Expression.unique_id_map and Expression.unique_id_map[self._unique_id] != self._unique_rep:
            self._unique_id += 1
        Expression.unique_id_map[self._unique_id] = self._unique_rep
    
    def __setattr__(self, attr, value):
        '''
        Expressions should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).
        '''
        if hasattr(self, attr):
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value      
    
    def __repr__(self):
        return str(self) # just use the string representation
    
    def __eq__(self, other):
        if isinstance(other, Expression):
            return self._unique_id == other._unique_id
        else: return False # other must be an Expression to be equal to self
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return self._unique_id
    
    def __str__(self):
        '''
        Return a string representation of the Expression.
        '''
        return self.string()

    def string(self, **kwargs):
        '''
        Return a string representation of the Expression.  The kwargs can contain formatting
        directives (such as 'fence' used to indicate when a sub-expression should be wrapped in
        parentheses if there can be ambiguity in the order of operations).
        '''
        raise NotImplementedError("'string' method not implemented for " + str(self.__class__))

    def latex(self, **kwargs):
        '''
        Return a latex-formatted representation of the Expression.  The kwargs can contain formatting
        directives (such as 'fence' used to indicate when a sub-expression should be wrapped in
        parentheses if there can be ambiguity in the order of operations).
        '''
        raise NotImplementedError("'latex' method not implemented for " + str(self.__class__))
    
    def formatted(self, formatType, **kwargs):
        '''
        Returns a formatted version of the expression for the given formatType
        ('string' or 'latex').  In the keyword arguments, fence=True indicates
        that parenthesis around the sub-expression may be necessary to avoid 
        ambiguity.
        '''
        if formatType == 'string': return self.string(**kwargs)
        if formatType == 'latex': return self.latex(**kwargs)
    
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        '''
        Should make the Expression object for the specific Expression sub-class based upon the coreInfo
        and subExpressions.  Must be implemented for each Expression sub-class that can be instantiated.
        '''
        raise MakeNotImplemented(subClass)
    
    def subExprIter(self):
        '''
        Iterator over the sub-expressions of this expression.
        '''
        return iter(self._subExpressions)
    
    def prove(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove this expression automatically under the
        given assumptions (if None, uses defaults.assumptions).  First
        it tries to find an existing KnownTruth, then it tries a simple
        proof by assumption (if self is contained in the assumptions),
        then it attempts to call the conclude method.  If successful,
        the KnownTruth is returned, otherwise an exception is raised.
        '''
        from proveit import KnownTruth
        assumptions = defaults.checkedAssumptions(assumptions)
        foundTruth = KnownTruth.findKnownTruth(self, assumptions)
        if foundTruth is not None: 
            return foundTruth # found an existing KnownTruth that does the job!
        if self in assumptions:
            # prove by assumption
            from proveit._core_.proof import Assumption
            return Assumption(self).provenTruth
        try:
            return self.conclude(assumptions)
        except NotImplementedError:
            raise ProofFailure('Unable to automatically prove ' + str(self) + ' assuming {' + ', '.join(str(assumption) for assumption in assumptions) + '}')
    
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude, via automation, that this statement is true
        under the given assumptions.  Return the KnownTruth if successful,
        or raise an exception.  This may be implemented for specific
        Expression classes (or will raise a NotImplementedError).
        '''
        raise NotImplementedError('The conclude method has not been implemented for ' + str(self.__class__))
    
    def deduceSideEffects(self, known_truth):
        '''
        Deduce side effects, obvious and useful consequences that may be arise from
        proving that this expression is a known truth (under some set of assumptions).
        The default is to do nothing, but should be overridden as appropriate.  
        There is no need to call this manually; it is called automatically when
        the corresponding KnownTruth is created.
        '''
        pass
        
    
    '''
    def beginProof(self):
        # clear all the provers
        from proveit._core_.known_truth import KnownTruth
        from proveit._core_.prover import Prover

        # forget that this is a theorem expression so that we generate a non-trivial proof:
        for stmt in KnownTruth.statements.values():
            # clear all of the statements to start fresh
            stmt.proofNumber = float('inf')
            stmt._prover = None
            if stmt == self.statement:
                stmt._isNamedTheorem = False
        Prover._tmpProvers.clear()
        for stmt in KnownTruth.statements.values():
            # re-mark the axioms and theorems as proven (but not the special one we are trying to prove)
            if stmt._isAxiom or stmt._isNamedTheorem:
                Prover._markAsProven(stmt, Prover(stmt, []))
                
        Expression.expr_to_prove = self
        return self
    
    def qed(self):
        """
        proofsdir, proofname = os.path.split(filename)
        # remove the file extension for the proof name
        proofname = os.path.splitext(proofname)[0]
        # remove any optional suffix after a space to go from the proof name to the theorem name
        thmname = os.path.splitext(proofname)[0].split()[0]
        theorems_abspath = os.path.abspath(os.path.join(proofsdir, '../theorems'))
        theorems_relpath =  os.path.relpath(theorems_abspath, start=os.path.join(os.path.split(proveit.__file__)[0], '..'))
        thm_import = __import__(theorems_relpath.replace(os.sep, '.'), fromlist=[thmname])
        try:
            thm = thm_import.__getattr__(thmname)
        except AttributeError:
            raise ProofFailure('Theorem named ' + thmname + ' does not exist')
        if not thm == self:
            raise ProofFailure('Theorem statement does not match qed expression:\n' + str(thm) + ' vs\n' + str(self))
        # forget that this is a theorem expression so that we generate a non-trivial proof:
        self.state()
        self.statement._prover = None
        self.proven()
        pvit_path = os.path.join(os.path.split(filename)[0], '..', '__pv_it__')
        pvit_proofs_path = os.path.join(pvit_path, 'proofs')
        if not os.path.exists(pvit_proofs_path):
            os.mkdir(pvit_proofs_path)
        expressions_dir = os.path.join(pvit_path, 'expressions')
        if not os.path.exists(expressions_dir):
            os.mkdir(expressions_dir)
        pvit_proof_filename = os.path.join(pvit_proofs_path, proofname + '.pv_it')
        with open(pvit_proof_filename, 'w') as pvit_proof_file:
            self.statement.getProver()._export_pvit(pvit_proofs_path, pvit_proof_file, expressions_dir)
        """
        if not Expression.expr_to_prove == self:
            raise ProofFailure('Theorem statement does not match qed expression:\n' + str(Expression.expr_to_prove) + ' vs\n' + str(self))
        self.proven()
        self.statement._getProver().showProof()
        return self
    '''
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the expressions substituted 
        according to the exprMap dictionary (mapping Expressions to Expressions --
        for specialize, this may only map Variables to Expressions).
        If supplied, reservedVars is a dictionary that maps reserved Variable's
        to relabeling exceptions.  You cannot substitute with an expression that
        uses a restricted variable and you can only relabel the exception to the
        restricted variable.  This is used to protect an Lambda function's "scope".
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return self
    
    def relabeled(self, relabelMap, reservedVars=None):
        '''
        A watered down version of substitution in which only variable labels are
        changed.  This may also involve substituting a MultiVariable with a list
        of Variables.
        '''
        return self.substituted(exprMap=dict(), relabelMap=relabelMap, reservedVars=reservedVars)
    
    def _validateRelabelMap(self, relabelMap):
        if len(relabelMap) != len(set(relabelMap.values())):
            raise ImproperRelabeling("Cannot relabel different Variables to the same Variable.")
    
    def usedVars(self):
        """
        Returns any variables used in the expression.
        """
        return set()
    
    def freeVars(self):
        """
        Returns the used variables that are not bound as an instance variable.
        """
        return set()    

    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        return set()    

    def safeDummyVar(self):
        from proveit._core_.expression.label.var import safeDummyVar
        return safeDummyVar(self)

    def safeDummyVars(self, n):
        from proveit._core_.expression.label.var import safeDummyVar
        dummyVars = []
        for _ in range (n):
            dummyVars.append(safeDummyVar(*([self] + dummyVars)))
        return dummyVars
    
    def relabel(self, relabelMap=None, assumptions=None):
        '''
        Performs a relabeling derivation step to be proven under the given
        assumptions (if None, uses defaults.assumptions).  Returns
        the proven relabeled KnownTruth, or throws an exception if the
        proof fails.
        '''
        return self._specialize_or_relabel(subMap=None, relabelMap=relabelMap, assumptions=assumptions)
    
    def specialize(self, subMap=None, relabelMap=None, assumptions=None):
        '''
        Performs a specialize derivation step to be proven under the given
        assumptions (if None, uses defaults.assumptions).  Returns
        the proven relabeled KnownTruth, or throws an exception if the
        proof fails.
        '''
        # Can be overridden by the Forall implementation
        return self._specialize_or_relabel(subMap=subMap, relabelMap=relabelMap, assumptions=assumptions)

    def _specialize_or_relabel(self, subMap=None, relabelMap=None, assumptions=None):
        from proveit._core_.proof import Specialization
        return Specialization(self, subMap, relabelMap, assumptions).provenTruth
    
    def proveByEval(self):
        '''
        Prove self by calling self.evaluate() if it equates the expression to TRUE.
        The evaluate method must be implemented by the derived class.
        '''
        return self.evaluate().deriveViaBooleanEquality()
    
    def _restrictionChecked(self, reservedVars):
        '''
        Check that a substituted expression (self) does not use any reserved variables
        (arguments of a Lambda function Expression).
        '''
        if not reservedVars is None and not self.freeVars().isdisjoint(reservedVars.keys()):
            raise ScopingViolation("Must not make substitution with reserved variables  (i.e., arguments of a Lambda function)")
        return self

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
        for sub_expr in self._subExpressions:
            sub_expr._config_latex_tool(lt)
    
    def exprInfo(self, details=False):
        from proveit._core_.expression.expr_info import ExpressionInfo
        return ExpressionInfo(self, details)
        
class MakeNotImplemented(NotImplementedError):
    def __init__(self, exprSubClass):
        self.exprSubClass = exprSubClass
    def __str__(self):
        return "make method not implemented for " + str(self.exprSubClass)

class ImproperSubstitution(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ImproperRelabeling(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ScopingViolation(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ProofFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
    
