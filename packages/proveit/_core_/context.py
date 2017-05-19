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

A _pv_it_ sub-directory is generated to store a distributed
"database" of information pertaining to the context.  It stores Expression
entries along with latex and png representations for convenience.  It
enumerates the Axioms and the Theorems, pointing to these Expression entries.
It also stores KnownTruth and Proof entries for the purpose of storing
the theorem proofs, and it stores theorem proof dependencies.
'''

import os
from storage import Storage

class Context:
    '''
    A Context object provides an interface into the _pv_it_ database for access
    to the common expressions, axioms, theorems and associated proofs of a
    Prove-It context.  You can also store miscellaneous expressions (and
    their latex/png representations) generated in test/demonstration notebooks 
    within the context directory.  These may be garbage collected via the
    'clean' method; anything that is not associated with a common
    expression, axiom, theorem, or theorem proof will be garbage collected.
    '''
    
    # track the storage object associated with each context, mapped
    # by the absolute path
    storages = dict()
    
    # externals.txt at top level to track relative path to external
    # contexts.
    def __init__(self, path='.'):
        '''
        Create a Context for the given path.  If no package
        is provided, base the context on the current working directory.
        '''
        abspath = os.path.abspath(path)
        # the name of the context is based upon the directory, going
        # up the tree as long as there is an __init__.py file.
        self.name = ''
        while os.path.isfile(os.path.join(path, '__init__.py')):
            path, tail = os.path.split(path)
            self.name = tail + '.' + self.name
        # the root context tracks paths to external packages
        if self.name == '':
            raise ContextException(self, 'Context directory must have an __init__.py file')
        if '.' in self.name:
            self.rootContext = Context(path)
        else:
            self.rootContext = self # this is a root context
        # Create the Storage object for this Context
        if abspath not in Context.storages:
            Context.storages[abspath] = Storage(self, abspath)
        self._storage = Context.storages[abspath]
        if self.name == '':
            self.name = os.path.split(path)[1]
        # map common expression names to storage identifiers:
        self.common_expr_ids = None # read in when needed
    
    def isRoot(self):
        '''
        Return True iff this Context is a "root" Context (no parent
        directory with an __init__.py file).
        '''
        return self.rootContext == self
    
    def getContext(self, context_name):
        split_context_name = context_name.split('.')
        if split_context_name[0] == self.rootContext.name:
            # Context with the same root as this one
            return Context(os.path.join(self._storage.directory, split_context_name[1:]))
        else:
            # Context with a different root than this one; need to get the path of the other root.
            self._storage
     
    def _setAxioms(self, axiom_definitions):
        self._setSpecialStatements(axiom_definitions, 'axioms')
    
    def _setTheorems(self, theorem_definitions):
        self._setSpecialStatements(theorem_definitions, 'theorems')
    
    def _setSpecialStatements(self, definitions, kind):
        storage = self._storage
        specialStatementsPath = os.path.join(storage.pv_it_dir, '_' + kind + '_')
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
                raise ContextException(self, 'corrupted _pv_it_ directory')
        # Remove the special statements that no longer exist
        for name in toRemove:
            print 'Removing %s %s from %s context'%(kind, name, self.name)
            self.getStoredStmt(self.name + '.' + name, kind[:-1]).remove()
            
        # Update the definitions
        for name, expr in definitions.iteritems():
            # add the expression to the "database" via the storage object.
            exprId = storage._proveItObjId(expr)
            if name in previousDefIds and previousDefIds[name] == exprId:
                continue # unchanged special statement
            storedSpecialStmt = self.getStoredStmt(self.name + '.' + name, kind[:-1])
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
        specialStatementsPath = os.path.join(storage.pv_it_dir, '_' + kind + '_')
        try:
            with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
                exprId = f.read()
                return storage.makeExpression(exprId)
        except IOError:
            raise KeyError("%s of name '%s' not found"%(kind[:-1], name))        

    def _getSpecialStatementNames(self, kind):
        specialStatementsPath = os.path.join(self._storage.pv_it_dir, '_' + kind + '_')
        return os.listdir(specialStatementsPath)
            
    def _setCommonExpressions(self, expr_definitions):
        self.common_expr_ids = dict()
        storage = self._storage
        commons_filename = os.path.join(self._storage.pv_it_dir, '_commons_.pv_it')
        with open(commons_filename, 'w') as f:
            for name, expr in expr_definitions.iteritems():
                exprId = storage._proveItObjId(expr)
                self.common_expr_ids[name] = exprId
                f.write(name + ' ' + exprId + '\n')
    
    def axiomNames(self):
        return self._getSpecialStatementNames('axioms')
    
    def theoremNames(self):
        return self._getSpecialStatementNames('theorems')
    
    def commonExpressionNames(self):
        self.common_expr_ids = dict()
        commons_filename = os.path.join(self._storage.pv_it_dir, '_commons_.pv_it')
        with open(commons_filename, 'r') as f:
            for line in f.readlines():
                name, exprId = line.split()
                self.common_expr_ids[name] = exprId
                yield name
    
    def getAxiom(self, name):
        '''
        Return the KnownTruth for the Axiom of the given name in this context.
        '''
        from proveit._core_.proof import Axiom
        expr = self._getSpecialStatementExpr('axioms', name)
        return Axiom(expr, self, name).provenTruth
        
    def getTheorem(self, name):
        '''
        Return the KnownTruth for the Theorem of the given name in this context.
        '''
        from proveit._core_.proof import Theorem
        expr = self._getSpecialStatementExpr('theorems', name)
        return Theorem(expr, self, name).provenTruth
    
    def getStoredAxiom(self, fullname):
        return self.getStoredStmt(fullname, 'axiom')

    def getStoredTheorem(self, fullname):
        return self.getStoredStmt(fullname, 'theorem')
                
    def getStoredStmt(self, fullname, kind):
        from storage import StoredAxiom, StoredTheorem
        split_name = fullname.split('.')
        context_name = '.'.join(split_name[:-1])
        stmt_name = split_name[-1]
        context = self.getContext(context_name)
        if kind == 'axiom':
            return StoredAxiom(context, stmt_name)
        elif kind == 'theorem':
            return StoredTheorem(context, stmt_name)
        else:
            raise ContextException(self, "Expecting kind to be 'axiom' or 'theorem' not '%s'"%kind)

    def getCommonExpr(self, name):
        '''
        Return the Expression of the common expression in this context
        with the given name.
        '''
        if self.common_expr_ids is None:
            # while the names are read in, the expr id map will be generated
            list(self.commonExpressionNames)
        # make the common expression for the given common expression name
        return self._storage.makeExpression(self.common_expr_ids[name])
    
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
        Create it if it did not previously exist using _generate_png.
        Return the png data and path where the png is stored as a tuple.
        '''
        return self._storage.retrieve_png(expr, latex, configLatexToolFn)        
    
    def clean(self):
        '''
        Clean the corresponding _pv_it_ directory of any stored expressions
        or proofs that have a reference count of zero.
        '''
        return self._storage.clean()

    def erase(self):
        '''
        Erase the corresponding _pv_it_ directory entirely.
        '''
        return self._storage.erase()        
        
class Axioms:
    '''
    Used in _axioms_.py modules for accessing Axioms from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, context):
        self._context = context

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.getAxiomNames())

    def __getattr__(self, name):
        try:
            axiom = self._context.getAxiom(name)
        except KeyError:
            raise AttributeError("'" + name + "' axiom not found in '" + self._package + "'\n(make sure to execute the appropriate '_axioms_.ipynb' notebook after any changes)")
        axiom.deriveSideEffects()
        return axiom
    
class Theorems:
    '''
    Used in _theorems_.py modules for accessing Theorems from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, context):
        self._context = context

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.getTheoremNames())
                
    def __getattr__(self, name):
        try:
            theorem = self._context.getTheorem(name)
        except KeyError:
            raise AttributeError("'" + name + "' theorem not found in '" + self._package +  "'\n(make sure to execute the appropriate '_theorems_.ipynb' notebook after any changes)")
        theorem.deriveSideEffects()
        return theorem

class CommonExpressions:
    '''
    Used in _common_.py modules for accessing common sub-expressions.
    '''
    def __init__(self, context):
        self._context = context

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.getCommonExpressionNames())

    def __getattr__(self, name):
        try:
            return self._context.getCommonExpression(name)
        except KeyError:
            raise AttributeError("'" + name + "' not found in the list of common expressions of '" + self._package + "'\n(make sure to execute the appropriate '_common_.ipynb' notebook after any changes)")

class ContextException(Exception):
    def __init__(self, context, message):
        self.directory = context._storage.directory
        self.message = message
        
    def __str__(self):
        return 'Context exception for %s: %s'%(self.directory, self.message)
