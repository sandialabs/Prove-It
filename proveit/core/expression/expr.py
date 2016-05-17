"""
This is the expression module.
"""

class Expression:
    unique_id_map = dict() # map unique_id's to unique_rep's
    expr_to_prove = None # the theorem currently being proven (if there is one)
    
    def __init__(self, coreInfo, subExpressions=tuple()):
        '''
        Initialize an expression with the given coreInfo (information relevant at the core Expression-type
        level) which should be a list (or tuple) of strings, and a list (or tuple) of subExpressions.
        '''
        # Will be the associated Statement if the Expression is
        # ever 'stated' in a particular prover.
        self.statement = None
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
        self.png = None # if a png is generate, it is stored for future reference
    
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
    
    """
    def _export_pvit(self, directory):
        '''
        Export the expression and sub-expressions into the given directory
        for the purposes of proof certification.  Returns the identifier of
        this expression, unique within the directory.  This occurs behind-the-
        scenes (and is therefore not a "public" method).
        '''
        import hashlib
        # export sub expressions and obtain their directory-unique ids
        sub_ids = [sub_expr._export_pvit(directory) for sub_expr in self._subExpressions]
        # generate a directory-unique representation for this expression
        unique_rep = self.__class__ + ' ' + self._coreInfo + ' ' + ', '.join(sub_id for sub_id in sub_ids) + '\n'
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        hash_dir = os.path.join(directory, rep_hash)
        if not os.path.exists(hash_dir):
            os.mkdir(hash_dir)
        # check for existing files in this hash value sub-directory (it may be there already)
        for expr_file in os.listdir(hash_dir):
            if expr_file[-6:] == '.pv_it':
                with open(os.path.join(hash_dir, expr_file), 'r') as f:
                    if f.read() == unique_rep:
                        # an existing file contains the exported expression
                        return rep_hash + '/' + expr_file[:-6]
        # does not exist, create a new file (checking against an unlikely collision)
        k = 0
        while os.path.exists(os.path.join(hash_dir, str(k) + '.pv_it')):
            k += 1
        with open(os.path.join(hash_dir, str(k) + '.pv_it'), 'w') as f:
            f.write(unique_rep)
        return rep_hash + '/' + str(k) # unique id
    """
    
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
    
    def subExprGen(self):
        '''
        Generator over the sub-expressions of this expression.
        '''
        for subExpr in self._subExpressions:
            yield subExpr
        
    def proven(self, assumptions=frozenset()):
        """
        Prove a step along the way to a theorem proof (or throw an error if the proof fails).
        Returns this proven statement expression.
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        if self.isProven(assumptions)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
    
    def beginProof(self):
        # clear all the provers
        from proveit.core.statement import Statement
        from proveit.core.prover import Prover

        # forget that this is a theorem expression so that we generate a non-trivial proof:
        for stmt in Statement.statements.values():
            # clear all of the statements to start fresh
            stmt.proofNumber = float('inf')
            stmt._prover = None
            if stmt == self.statement:
                stmt._isNamedTheorem = False
        Prover._tmpProvers.clear()
        for stmt in Statement.statements.values():
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
        self.statement.getProver().showProof()
        return self
    
    def checked(self, assumptions=frozenset()):
        """
        Check that this statement is true under the given assumptions but not for a step
        of a theorem proof (that is, temporary provers aren't stored).  Returns
        this checked statement expression.
        """
        def makeAssumptionsStr(assumption):
            return "{" + ", ".join([str(assumption) for assumption in assumptions]) + "}"
        if self.isProven(assumptions, markProof=False)==False:
            raise ProofFailure("Proof failed: " + str(self) + " assuming " + makeAssumptionsStr(assumptions))
        return self
        
    def isProven(self, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to proven this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.
        """
        from proveit.core.statement import Statement
        if self.statement == None: Statement.state(self)
        if not isinstance(self.statement, Statement):
            raise TypeError('Expression statement must be of Statement type')
        return self.statement.isProven(assumptions, maxDepth, markProof)
    
    def wasProven(self, assumptions=frozenset()):
        """
        Returns True iff this statement has already be proven under the given assumptions.
        """
        from proveit.core.statement import Statement
        if self.statement == None:
            return False
        else:
            if not isinstance(self.statement, Statement):
                raise TypeError('Expression statement must be of Statement type')
            return self.statement.wasProven(assumptions)
        
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
        from proveit.core.expression.label.var import safeDummyVar
        return safeDummyVar(self)

    def safeDummyVars(self, n):
        from proveit.core.expression.label.var import safeDummyVar
        dummyVars = []
        for _ in range (n):
            dummyVars.append(safeDummyVar(*([self] + dummyVars)))
        return dummyVars
    
    def state(self):
        from proveit.core.statement import Statement
        return Statement.state(self)

    def relabel(self, relabelMap=None):
        return self._specialize_or_relabel(subMap=None, relabelMap=relabelMap)
    
    def specialize(self, subMap=None, relabelMap=None):
        # Can be overridden by the Forall implementation
        return self._specialize_or_relabel(subMap=subMap, relabelMap=relabelMap)

    def _specialize_or_relabel(self, subMap=None, relabelMap=None):
        from proveit.core.statement import Statement
        if subMap is None: subMap = dict()
        if relabelMap is None: relabelMap = dict()
        (specialization, conditions) = Statement.specialize(self, subMap, relabelMap)
        return specialization.checked({self} | conditions)
        
    def generalize(self, forallVars, domain=None, conditions=tuple()):
        from proveit.core.statement import Statement
        from proveit.core.expression.composite.composite import compositeExpression
        # Note that the prover will not pass this "checked" in its current implementation
        # because it will not allow assumptions with variables in the newly created scope.
        # The solution for now is not to bother calling "checked" here.
        return Statement.generalize(self, compositeExpression(forallVars), domain, conditions)#.checked({self})
    
    """
    def show(self, assumptions=frozenset()):
        '''
        Show the derivation tree of the proof or partial proof for
        proving the Statement of this Expression under the given
        assumptions.
        '''
        from derivationTreeView import showTreeView
        showTreeView([self.state().statement.getOrMakeProver(assumptions)])
    
    def proveThenShow(self, assumptions=frozenset()):
        '''
        First attempt to proven the Statement of this Expression, then
        show the derivation tree of the proof.
        '''
        self.proven(assumptions).show(assumptions)
    """
    
    def proveByEval(self):
        '''
        Prove self by calling self.evaluate() if it equates the expression to TRUE.
        The evaluate method must be implemented by the derived class.
        '''
        return self.evaluate().deriveViaBooleanEquality().proven()
    
    def _restrictionChecked(self, reservedVars):
        '''
        Check that a substituted expression (self) does not use any reserved variables
        (arguments of a Lambda function Expression).
        '''
        if not reservedVars is None and not self.freeVars().isdisjoint(reservedVars.keys()):
            raise ScopingViolation("Must not make substitution with reserved variables  (i.e., arguments of a Lambda function)")
        return self

    # THIS USES MATHJAX WHICH IS LESS FLEXIBLE THAN DVIPNG (BELOW)  
    """
    def _repr_latex_(self):
        return '$' + self.formatted(LATEX) + '$'
    """
    def _repr_png_(self):
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        if not hasattr(self,'png') or self.png is None:
            LaTeXTool.clear_instance()
            lt = LaTeXTool.instance()
            lt.use_breqn = False
            self._config_latex_tool(lt)
            self.png = latex_to_png(self.latex(), backend='dvipng', wrap=True)
        return self.png
    
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        for sub_expr in self._subExpressions:
            sub_expr._config_latex_tool(lt)
    
    def exprTree(self):
        from expr_tree import ExpressionTree
        return ExpressionTree(self)
        
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
