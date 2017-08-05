'''
A context in Prove-It is a conceptual space of related literals, axioms,
and theorems.  Consider, for example, a mathematics subject area such
as trigonometry or linear algebra.  A context could represent such a
subject area, or a reasonable subset of such a subject area.  Such
contexts are represented in directories.  The directory will contain 
Jupyter notebooks for common expressions (_common_.ipynb) including 
literals, axioms (_axioms_.ipynb), and theorems (_theorems_.ipynb).  It
will also contain Python scripts for defining Operation or Literal classes
for building Expression objects specific to the context with convenient
methods for invoking theorems and automated derivations.  Proofs of
the theorems are to be stored in a _proofs_ sub-directory as Jupyter
notebooks named for the theorem to be proven.

A __pv_it sub-directory is generated to store a distributed
"database" of information pertaining to the context.  It stores Expression
entries along with latex and png representations for convenience.  It
enumerates the Axioms and the Theorems, pointing to these Expression entries.
It also stores KnownTruth and Proof entries for the purpose of storing
the theorem proofs, and it stores theorem proof dependencies.
'''

import os
from glob import glob
from storage import Storage

class Context:
    '''
    A Context object provides an interface into the __pv_it database for access
    to the common expressions, axioms, theorems and associated proofs of a
    Prove-It context.  You can also store miscellaneous expressions (and
    their latex/png representations) generated in test/demonstration notebooks 
    within the context directory.  These may be garbage collected via the
    'clean' method; anything that is not associated with a common
    expression, axiom, theorem, or theorem proof will be garbage collected.
    '''
    
    # maps root context names to their directories.  A root context
    # is one use containing directory has no __init__.py.  All context
    # directories should have an __init__.py file.
    _rootContextPaths = dict()
    
    # The current default Context when a Literal is created.
    # If this is None, use Context(), the Context at the current working directory.
    default = None
    
    # track the storage object associated with each context, mapped
    # by the absolute path
    storages = dict()

    specialExprKindToModuleName = {'common':'_common_', 'axiom':'_axioms_', 'theorem':'_theorems_'}
        
    # externals.txt at top level to track relative path to external
    # contexts.
    def __init__(self, path='.'):
        '''
        Create a Context for the given path.  If given a file name instead,
        use the path of the containing directory.  If no path
        is provided, base the context on the current working directory.
        '''
        path = os.path.abspath(path)
        # if in a __pv_it_ directory, go to the containing context directory
        splitpath = path.split(os.path.sep)
        if '__pv_it' in splitpath:
            num_up_levels = (len(splitpath)-splitpath.index('__pv_it'))
            path = os.path.abspath(os.path.join(*([path] + ['..']*num_up_levels)))
        # if in a _proofs_ directory, go to the containing context directory
        if splitpath[-1] == '_proofs_':
            path = os.path.abspath(os.path.join(*([path] + ['..'])))
        # Makes the case be consistent in operating systems (i.e. Windows)
        # with a case insensitive filesystem: 
        path = os.path.normcase(path)
        if os.path.isfile(path):
            path, _ = os.path.split(path)
        # the name of the context is based upon the directory, going
        # up the tree as long as there is an __init__.py file.
        self.name = ''
        remainingPath = path
        while os.path.isfile(os.path.join(remainingPath, '__init__.py')):
            remainingPath, tail = os.path.split(remainingPath)
            self.name = tail if self.name=='' else (tail + '.' + self.name)
        # the root context tracks paths to external packages
        if self.name == '':
            self.name = path
            raise ContextException('%s context directory must have an __init__.py file'%path)
        if '.' in self.name:
            rootDirectory = os.path.join(remainingPath, self.name.split('.')[0])
            self.rootContext = Context(rootDirectory)
        else:
            self.rootContext = self # this is a root context
        # Create the Storage object for this Context
        if path not in Context.storages:
            Context.storages[path] = Storage(self, path)
        self._storage = Context.storages[path]
        
        # map common expression names to storage identifiers:
        self._common_expr_ids = None # read in when needed
        
        # Map 'common', 'axiom', and 'theorem' to respective modules.
        # Base it upon the context name.
        self._specialExprModules = {kind:self.name+'.%s'%module_name for kind, module_name in Context.specialExprKindToModuleName.iteritems()}
    
    def __eq__(self, other):
        return self._storage is other._storage
    
    def __ne__(self, other):
        return self._storage is not other._storage
    
    def __str__(self):
        return self.name
    
    def isRoot(self):
        '''
        Return True iff this Context is a "root" Context (no parent
        directory with an __init__.py file).
        '''
        return self.rootContext is self
    
    def getPath(self):
        '''
        Return the directory associated with the context
        '''
        return self._storage.directory

    @staticmethod
    def setRootContextPath(contextName, path):
        path = os.path.normpath(os.path.abspath(path))
        if contextName in Context._rootContextPaths:
            storedPath = Context._rootContextPaths[contextName]
            if storedPath != path:
                raise ContextException("Conflicting directory references to context '%s': %s vs %s"%(contextName, path, storedPath))
        Context._rootContextPaths[contextName] = path 
    
    @staticmethod
    def getContext(contextName):
        '''
        Return the Context with the given name.
        '''
        splitContextName = contextName.split('.')
        rootName = splitContextName[0]
        if rootName not in Context._rootContextPaths:
            raise ContextException("Context root '%s' is unknown"%rootName)
        rootDirectory = Context._rootContextPaths[rootName]
        return Context(os.path.join(*([rootDirectory]+splitContextName[1:])))        
         
    def _setAxioms(self, axiomNames, axiomDefinitions):
        self._setSpecialStatements(axiomNames, axiomDefinitions, 'axiom')
    
    def _setTheorems(self, theoremNames, theoremDefinitions):
        self._setSpecialStatements(theoremNames, theoremDefinitions, 'theorem')
    
    def _setSpecialStatements(self, names, definitions, kind):
        storage = self._storage
        specialStatementsPath = os.path.join(storage.pv_it_dir, '_' + kind + 's_')
        if not os.path.isdir(specialStatementsPath):
            os.mkdir(specialStatementsPath)
        # First get the previous special statement definitions to find out what has been added/changed/removed
        previousDefIds = dict()
        toRemove = []
        for name in os.listdir(specialStatementsPath):
            try:
                with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
                    if name not in definitions:
                        toRemove.append(name) # to remove special statement that no longer exists
                    previousDefIds[name] = f.read()
            except IOError:
                raise ContextException('Corrupted __pv_it directory: %s'%self._storage.directory)
        # Remove the special statements that no longer exist
        for name in toRemove:
            print 'Removing %s %s from %s context'%(kind, name, self.name)
            Context.getStoredStmt(self.name + '.' + name, kind).remove()
            
        # Update the definitions
        for name in names:
            expr = definitions[name]
            # record the special expression in this context object
            if not hasattr(expr, 'context'):                
                expr.context = self
                self._storage.specialExpressions[expr] = (kind, name)            
            # add the expression to the "database" via the storage object.
            exprId = storage._proveItStorageId(expr)
            if name in previousDefIds and previousDefIds[name] == exprId:
                continue # unchanged special statement
            storedSpecialStmt = Context.getStoredStmt(self.name + '.' + name, kind)
            if name not in previousDefIds:
                # added special statement
                print 'Adding %s %s to %s context'%(kind, name, self.name)
            elif previousDefIds[name] != exprId:
                # modified special statement. remove the old one first.
                print 'Modifying %s %s in %s context'%(kind, name, self.name)
                storedSpecialStmt.remove(keepPath=True)
            # record the axiom/theorem id (creating the directory if necessary)
            specialStatementDir = os.path.join(specialStatementsPath, name)
            if not os.path.isdir(specialStatementDir):
                os.mkdir(specialStatementDir)
            with open(os.path.join(specialStatementDir, 'expr.pv_it'), 'w') as exprFile:
                exprFile.write(exprId)
                storage._addReference(exprId)
            with open(os.path.join(specialStatementDir, 'usedBy.txt'), 'w') as exprFile:
                pass # usedBy.txt must be created but initially empty
        
    def _getSpecialStatementExpr(self, kind, name):
        storage = self._storage
        specialStatementsPath = os.path.join(storage.pv_it_dir, '_' + kind + 's_')
        try:
            with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
                exprId = f.read()
                expr = storage.makeExpression(exprId)
                if not hasattr(expr, 'context'):                
                    expr.context = self
                    self._storage.specialExpressions[expr] = (kind, name)
                return expr
        except IOError:
            raise KeyError("%s of name '%s' not found"%(kind, name))        

    def _getSpecialStatementNames(self, kind):
        specialStatementsPath = os.path.join(self._storage.pv_it_dir, '_' + kind + 's_')
        return os.listdir(specialStatementsPath)
            
    def _setCommonExpressions(self, exprNames, exprDefinitions):
        self._common_expr_ids = dict()
        storage = self._storage
        commons_filename = os.path.join(self._storage.pv_it_dir, '_commons_.pv_it')
        
        # get any previous common expression ids to see if their reference
        # count needs to be decremented.
        old_expr_ids = set() 
        if os.path.isfile(commons_filename):
            with open(commons_filename, 'r') as f:
                for line in f.readlines():
                    name, expr_id = line.split()
                    old_expr_ids.add(expr_id)
        
        # write new common expression ids
        new_expr_ids = set()
        with open(commons_filename, 'w') as f:
            for name in exprNames:
                expr = exprDefinitions[name]
                # record the special expression in this context object
                if not hasattr(expr, 'context'): expr.context = self
                self._storage.specialExpressions[expr] = ('common', name) 
                # get the expression id to be stored on '_commons_.pv_it'           
                expr_id = storage._proveItStorageId(expr)
                if expr_id in old_expr_ids:
                    old_expr_ids.remove(expr_id) # same expression as before
                else:
                    # new expression not previously in the common expressions liest:
                    new_expr_ids.add(expr_id) 
                self._common_expr_ids[name] = expr_id
                f.write(name + ' ' + expr_id + '\n')
        
        # remove references to old common expressions that are no longer a common expression
        for expr_id in old_expr_ids:
            storage._removeReference(expr_id, removingSpecialExpr=True) # remove reference to an old common expression
        
        # add references to new common expressions that were not preveiously a common expression
        for expr_id in new_expr_ids:
            storage._addReference(expr_id) # add reference to a new common expression
    
    def axiomNames(self):
        return self._getSpecialStatementNames('axiom')
    
    def theoremNames(self):
        return self._getSpecialStatementNames('theorem')
    
    def commonExpressionNames(self):
        self._common_expr_ids = dict()
        commons_filename = os.path.join(self._storage.pv_it_dir, '_commons_.pv_it')
        if os.path.isfile(commons_filename):
            with open(commons_filename, 'r') as f:
                for line in f.readlines():
                    name, exprId = line.split()
                    self._common_expr_ids[name] = exprId
                    yield name
    
    def getAxiom(self, name):
        '''
        Return the Axiom of the given name in this context.
        '''
        from proveit._core_.proof import Axiom
        expr = self._getSpecialStatementExpr('axiom', name)
        return Axiom(expr, self, name)
        
    def getTheorem(self, name):
        '''
        Return the Theorem of the given name in this context.
        '''
        from proveit._core_.proof import Theorem
        expr = self._getSpecialStatementExpr('theorem', name)
        return Theorem(expr, self, name)
    
    def specialExpr(self, expr):
        '''
        Return the kind and name of the special expression as a tuple,
        assuming the 'expr' is a special expression of this Context.
        '''
        return self._storage.specialExpressions[expr]
    
    def specialExprAddress(self, expr):
        '''
        A special expression "address" consists of a module and the name 
        of the expression.
        Provided that the given expression is one of the special expressions
        of this context, return the address as a tuple.
        '''
        kind, name = self._storage.specialExpressions[expr]
        if kind == 'axiom' or kind=='theorem':
            name = name + '.expr'
        return self._specialExprModules[kind], name
    
    def proofNotebook(self, theoremName, expr):
        '''
        Return the path of the proof notebook for a theorem with the given
        name and expression, creating it if it does not already exist.
        '''
        return self._storage.proofNotebook(theoremName, expr)

    def stashExtraneousProofNotebooks(self):
        '''
        For any proof notebooks for theorem names not included in the context, 
        stash them or remove them if they are generic notebooks.
        '''
        self._storage.stashExtraneousProofNotebooks(self.theoremNames())
                
    def expressionNotebook(self, expr, unofficialNameKindContext=None):
        '''
        Return the path of the expression notebook, creating it if it does not
        already exist.  If 'unofficialNameKindContext' is provided,
        it should be the (name, kind, context) for a special expression
        that is not-yet-official (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        # use the Storage object to generate/grab the expression notebook.
        return self._storage.expressionNotebook(expr, unofficialNameKindContext)        
                
    @staticmethod
    def getStoredAxiom(fullname):
        return Context.getStoredStmt(fullname, 'axiom')

    @staticmethod
    def getStoredTheorem(fullname):
        return Context.getStoredStmt(fullname, 'theorem')
                
    @staticmethod
    def getStoredStmt(fullname, kind):
        from storage import StoredAxiom, StoredTheorem
        split_name = fullname.split('.')
        context_name = '.'.join(split_name[:-1])
        stmt_name = split_name[-1]
        context = Context.getContext(context_name)
        if kind == 'axiom':
            return StoredAxiom(context, stmt_name)
        elif kind == 'theorem':
            return StoredTheorem(context, stmt_name)
        else:
            raise ContextException("Expecting 'kind' to be 'axiom' or 'theorem' not '%s'"%kind)

    def getCommonExpr(self, name):
        '''
        Return the Expression of the common expression in this context
        with the given name.
        '''
        if self._common_expr_ids is None:
            # while the names are read in, the expr id map will be generated
            list(self.commonExpressionNames())
        # make the common expression for the given common expression name
        prev_context_default = Context.default
        Context.default = self # set the default Context in case there is a Literal
        try:
            expr = self._storage.makeExpression(self._common_expr_ids[name])
        finally:
            Context.default = prev_context_default # reset the default Context 
        if not hasattr(expr, 'context'):
            expr.context = self
        self._storage.specialExpressions[expr] = ('common', name)
        return expr
    
    def getStoredExpr(self, expr_id):
        '''
        Return the stored Expression with the given id (hash string).
        '''
        return self._storage.makeExpression(expr_id)
    
    def _includeMutualReferences(self, otherContext):
        '''
        Include a reference between contexts if they have a different root.
        '''
        if self.rootContext._storage is not otherContext.rootContext._storage:
            self.rootContext._storage.includeReference(otherContext.rootContext._storage)
            otherContext.rootContext._storage.includeReference(self.rootContext._storage)
    
    def _stored_png(self, expr, latex, configLatexToolFn):
        '''
        Find the .png file for the stored Expression.
        Create it if it did not previously exist.
        Return the png data and path where the png is stored as a tuple.
        '''
        return self._storage.retrieve_png(expr, latex, configLatexToolFn)        
    
    def clean(self):
        '''
        Clean the corresponding __pv_it directory of any stored expressions
        or proofs that have a reference count of zero.
        '''
        return self._storage.clean()

    def erase(self):
        '''
        Erase the corresponding __pv_it directory entirely.
        '''
        return self._storage.erase()        
        
class Axioms:
    '''
    Used in _axioms_.py modules for accessing Axioms from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, filename):
        self.context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + self.context.axiomNames())

    def __getattr__(self, name):
        try:
            axiom_truth = self.context.getAxiom(name).provenTruth
        except KeyError:
            raise AttributeError("'" + name + "' axiom not found in '" + self.context.name + "'\n(make sure to execute the appropriate '_axioms_.ipynb' notebook after any changes)")
        axiom_truth.deriveSideEffects()
        return axiom_truth
    
class Theorems:
    '''
    Used in _theorems_.py modules for accessing Theorems from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, filename):
        self.context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.theoremNames())
                
    def __getattr__(self, name):
        try:
            theorem_truth = self.context.getTheorem(name).provenTruth
        except KeyError:
            raise AttributeError("'" + name + "' theorem not found in '" + self.context.name +  "'\n(make sure to execute the appropriate '_theorems_.ipynb' notebook after any changes)")
        theorem_truth.deriveSideEffects()
        return theorem_truth

class CommonExpressions:
    '''
    Used in _common_.py modules for accessing common sub-expressions.
    '''
    def __init__(self, filename):
        self.context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + list(self.context.commonExpressionNames()))

    def __getattr__(self, name):
        try:
            return self.context.getCommonExpr(name)
        except KeyError:
            raise AttributeError("'" + name + "' not found in the list of common expressions of '" + self.context.name + "'\n(make sure to execute the appropriate '_common_.ipynb' notebook after any changes)")

class ContextException(Exception):
    def __init__(self, message):
        self.message = message
        
    def __str__(self):
        return self.message
