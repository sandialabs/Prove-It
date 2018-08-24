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
import json
from ._context_storage import ContextStorage

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
        
        # move the path up to the directory level, not script file level
        if path[-3:]=='.py' or path[-4:]=='.pyc':
            path, _ = os.path.split(path)
            
        if path in Context.storages:
            self._storage = Context.storages[path] # got the storage - we're good
            self.name = self._storage.name
            return
        
        if os.path.isfile(path): # just in case checking for '.py' or '.pyc' wasn't sufficient
            path, _ = os.path.split(path)

        if path in Context.storages:
            self._storage = Context.storages[path] # got the storage - we're good
            self.name = self._storage.name
            return
        
        # the name of the context is based upon the directory, going
        # up the tree as long as there is an __init__.py file.
        name = ''
        remainingPath = path
        while os.path.isfile(os.path.join(remainingPath, '__init__.py')):
            remainingPath, tail = os.path.split(remainingPath)
            name = tail if name=='' else (tail + '.' + name)
        # the root context tracks paths to external packages
        if name == '':
            name = path
            raise ContextException('%s context directory must have an __init__.py file'%path)
        rootDirectory = None
        if '.' in name:
            rootDirectory = os.path.join(remainingPath, name.split('.')[0])
        # Create the Storage object for this Context
        if path not in Context.storages:
            Context.storages[path] = ContextStorage(self, name, path, rootDirectory)
            # if the _sub_contexts_.txt file has not been created, make an empty one
            sub_contexts_path = os.path.join(path, '_sub_contexts_.txt')
            if not os.path.isfile(sub_contexts_path):
                open(sub_contexts_path, 'wt').close()
        self._storage = Context.storages[path]
        self.name = self._storage.name
            
    def __eq__(self, other):
        return self._storage is other._storage
    
    def __ne__(self, other):
        return self._storage is not other._storage
    
    def __str__(self):
        return self._storage.name
    
    def links(self, from_directory='.'):
        context_name_segments = self._storage.name.split('.')
        context_html_segments = []
        for k, context_name_segment in enumerate(context_name_segments):      
            path = os.path.join(*([self._storage.directory] + ['..']*(len(context_name_segments) - k - 1) + ['_context_.ipynb']))
            relpath = os.path.relpath(path, start=from_directory)
            context_html_segments.append(r'<a class=\"ProveItLink\" href=\"%s\">%s</a>'%(json.dumps(relpath).strip('"'), context_name_segment))
        return '.'.join(context_html_segments)
    
    def isRoot(self):
        '''
        Return True iff this Context is a "root" Context (no parent
        directory with an __init__.py file).
        '''
        return self._storage.isRoot()
    
    def getPath(self):
        '''
        Return the directory associated with the context
        '''
        return self._storage.directory

    @staticmethod
    def _setRootContextPath(contextName, path):
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
        
    def getSubContextNames(self):
        return self._storage.getSubContextNames()

    def getSubContexts(self):
        '''
        Yield the Context objects for the sub-contexts.
        '''
        for sub_context_name in self._storage.getSubContextNames():
            yield Context(os.path.join(self._storage.directory, sub_context_name))

    def setSubContextNames(self, subContextNames):
        return self._storage.setSubContextNames(subContextNames)

    def appendSubContextName(self, subContextName):
        return self._storage.appendSubContextName(subContextName)
                
    def _setAxioms(self, axiomNames, axiomDefinitions):
        self._storage.setSpecialStatements(axiomNames, axiomDefinitions, 'axiom')
    
    def _setTheorems(self, theoremNames, theoremDefinitions):
        self._storage.setSpecialStatements(theoremNames, theoremDefinitions, 'theorem')
    
    def _clearAxioms(self):
        self._setAxioms([], dict())

    def _clearTheorems(self):
        self._setTheorems([], dict())
    
            
    def _clearCommonExressions(self):
        self._setCommonExpressions([], dict(), clear=True)
        
    def _setCommonExpressions(self, exprNames, exprDefinitions, clear=False):
        self._storage.setCommonExpressions(exprNames, exprDefinitions, clear)
    
    def makeSpecialExprModule(self, kind):
        '''
        Make a _common_.py, _axioms_.py, or _theorems_.py file for importing
        expressions from the certified database.
        '''
        specialStatementsClassName = kind[0].upper() + kind[1:]
        if kind=='common': specialStatementsClassName = 'CommonExpressions'        
        output = "import sys\n"
        output += "from proveit._core_.context import %s\n"%specialStatementsClassName
        output += "sys.modules[__name__] = %s(__file__)\n"%(specialStatementsClassName)        
        filename = os.path.join(self._storage.directory, '_%s_.py'%kind)
        if os.path.isfile(filename):
            with open(filename, 'r') as f:
                if f.read() != output:
                    raise ContextException("An existing _%s_.py must be removed before a proper one may be autogenerated"%kind)
        else:        
            with open(filename, 'w') as f:
                f.write(output)
    
    def axiomNames(self):
        return list(self._storage.getSpecialStatementNames('axiom'))
    
    def theoremNames(self):
        return list(self._storage.getSpecialStatementNames('theorem'))
    
    def commonExpressionNames(self):
        return self._storage.commonExpressionNames()
    
    def recordCommonExprDependencies(self):
        '''
        Record the context names of any referenced common expressions in storage
        while creating the common expressions for this context
        (for the purposes of checking for illegal cyclic dependencies).
        '''
        self._storage.recordCommonExprDependencies()

    def storedCommonExprDependencies(self):
        '''
        Return the stored set of context names of common expressions
        referenced by the common expressions of this context.
        '''
        return self._storage.storedCommonExprDependencies()    

    def cyclicallyReferencedCommonExprContext(self):
        '''
        Check for illegal cyclic dependencies of common expression notebooks.
        If there is one, return the name; otherwise return None.
        '''
        return self._storage.cyclicallyReferencedCommonExprContext()
        
    def referenceDisplayedExpressions(self, name, clear=False):
        '''
        Reference displayed expressions, recorded under the given name
        in the __pv_it directory.  If the same name is reused,
        any expressions that are not displayed this time that
        were displayed last time will be unreferenced.
        If clear is True, remove all of the references and the
        file that stores these references.
        '''
        self._storage.referenceDisplayedExpressions(name, clear)
                            
    def getAxiom(self, name):
        '''
        Return the Axiom of the given name in this context.
        '''
        return self._storage.getAxiom(name)
            
    def getTheorem(self, name):
        '''
        Return the Theorem of the given name in this context.
        '''
        return self._storage.getTheorem(name)
    
    @staticmethod
    def findAxiom(fullName):
        '''
        Given the full name of an axiom that includes the context
        name, return the Axiom obtained the proper Context.
        '''
        return Context._findStmt(fullName, 'axiom')

    @staticmethod
    def findTheorem(fullName):
        '''
        Given the full name of an theorem that includes the context
        name, return the Theorem obtained the proper Context.
        '''
        return Context._findStmt(fullName, 'theorem')

    @staticmethod
    def _findStmt(fullName, kind):
        split_name = fullName.split('.')
        context_name, stmt_name = '.'.join(split_name[:-1]), split_name[-1]
        context = Context.getContext(context_name)
        if kind == 'axiom': return context.getAxiom(stmt_name)
        if kind == 'theorem': return context.getTheorem(stmt_name)

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
        return self._storage._specialExprModules[kind], name
    
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
        from _context_storage import StoredAxiom, StoredTheorem
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
        return self._storage.getCommonExpr(name)
    
    def getStoredExpr(self, expr_id):
        '''
        Return the stored Expression with the given id (hash string).
        '''
        return self._storage.makeExpression(expr_id)
    
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
    
    def clear(self):
        '''
        Remove reference counts to all common expressions, axioms,
        theorems, and recorded displayed expressions and then
        clean the __pv_it folder of any stored expressions with
        zero reference counts.  Note that this can, in principle
        (assuming nothing is corrupted), be undone by re-executing
        the notebooks that generated these in the first place.
        '''
        self._setTheorems([], dict())
        self._setAxioms([], dict())
        self._setCommonExpressions([], dict())
        self._storage.clearDisplayedExpressionReferences()
        self.clean()
        
    def clearAll(self):
        '''
        Clear (see clear method) this context and all sub-contexts.
        '''
        for sub_context in self.getSubContexts():
            sub_context.clear()
        self.clear()

    def containsAnyExpression(self):
        '''
        Return True if this context and all of its sub-contexts
        contain no expressions.
        '''
        if self._storage.containsAnyExpression():
            return True
        for sub_context in self.getSubContexts():
            if sub_context.containsAnyExpression():
                return True
        return False                    

class Axioms:
    '''
    Used in _axioms_.py modules for accessing Axioms from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, filename):
        self._context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.axiomNames())

    def __getattr__(self, name):
        try:
            axiom_truth = self._context.getAxiom(name).provenTruth
        except KeyError:
            raise AttributeError("'" + name + "' axiom not found in '" + self._context.name + "'\n(make sure to execute the appropriate '_axioms_.ipynb' notebook after any changes)")
        """
        try:
            axiom_truth.deriveSideEffects()
        except Exception as e:
            print "Failure to derive side effects of axiom", name
            traceback.print_exc()
            raise e
        """
        return axiom_truth
    
class Theorems:
    '''
    Used in _theorems_.py modules for accessing Theorems from
    the _certified_ database (returning the associated KnownTruth object).
    '''
    def __init__(self, filename):
        self._context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + self._context.theoremNames())
                
    def __getattr__(self, name):
        try:
            theorem_truth = self._context.getTheorem(name).provenTruth
        except KeyError:
            raise AttributeError("'" + name + "' theorem not found in '" + self._context.name +  "'\n(make sure to execute the appropriate '_theorems_.ipynb' notebook after any changes)")
        """
        try:
            theorem_truth.deriveSideEffects()
        except Exception as e:
            print "Failure to derive side effects of theorem", name
            traceback.print_exc()
            raise e
        """
        return theorem_truth

class CommonExpressions:
    '''
    Used in _common_.py modules for accessing common sub-expressions.
    '''
    
    # map storage ids of common expression to the Context of the common expression
    expr_id_contexts = dict() # populated in Context.commonExpressionNames()
    
    # set of contexts that has a common expression being referenced
    referenced_contexts = set() # populated in Storage._addReference(...)
    
    def __init__(self, filename):
        self._context = Context(filename)
        self.__file__ = filename

    def __dir__(self):
        return sorted(self.__dict__.keys() + list(self._context.commonExpressionNames()))

    def __getattr__(self, name):
        from proveit import Label
        # Is the current directory a "context" directory?
        in_context = os.path.isfile('_context_.ipynb')
        
        # File to store information about a failure to import a common expression:
        failed_common_import_filename = os.path.join('__pv_it', 'failed_common_import.txt')
        # This is used to track dependencies which automatically executing 
        # notebooks via 'build.py' (at the root level of Prove-It).
        
        try:
            expr = self._context.getCommonExpr(name)
            if in_context and os.path.isfile(failed_common_import_filename):
                # successful import -- don't need this 'failure' file anymore.
                os.remove(failed_common_import_filename)
            return expr
        except (UnsetCommonExpressions, KeyError) as e:
            # if this is a context directory, store the context that failed to import.
            if in_context:
                # store the context in which a common expression failed to import.
                with open(failed_common_import_filename, 'w') as f:
                    f.write(self._context.name + '\n')
            
            if isinstance(e, UnsetCommonExpressions):
                # Use a temporary placeholder if the common expressions are not set.
                # This avoids exceptions while common exppressions are being built/rebuilt.
                return Label("Temporary_placeholder_for_undefined_%s.%s"%(self._context.name, name), "Temporary\_placeholder\_for\_undefined\_%s.%s"%(self._context.name, name))
            
            raise AttributeError("'" + name + "' not found in the list of common expressions of '" + self._context.name + "'\n(make sure to execute the appropriate '_common_.ipynb' notebook after any changes)")

class ContextException(Exception):
    def __init__(self, message):
        self.message = message
        
    def __str__(self):
        return self.message


class UnsetCommonExpressions(Exception):
    def __init__(self, context_name):
        self.context_name = context_name
        
    def __str__(self):
        return "The common expressions in '%s' have not been set"%self.context_name