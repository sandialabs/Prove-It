import hashlib, os
import shutil
import sys
import importlib
import itertools
import time
import json
import re
import urllib.request, urllib.parse, urllib.error
import imp

def relurl(path, start='.'):
    '''
    Return the relative path as a url
    '''
    return urllib.request.pathname2url(os.path.relpath(path, start))

class ContextStorage:
    '''
    Manages the __pv_it directory of a Context, the distributed database
    of expressions, axioms, theorems, and proofs.  Additionally manages
    the _sub_contexts_.txt file which is in the main directory because it
    should be committed to the repository (unlike the __pv_it directory
    which can all be re-generated).
    '''

    def __init__(self, context, name, directory, rootDirectory):
        from .context import Context, ContextException
        if not isinstance(context, Context):
            raise ContextException("'context' should be a Context object")
        self.context = context
        self.name = name
        if rootDirectory is None:
            self.rootContextStorage = self
        else:
            self.rootContextStorage = Context(rootDirectory)._storage
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '__pv_it')
        self.referenced_dir = os.path.join(self.pv_it_dir, '_referenced_')
        if not os.path.isdir(self.referenced_dir):
            # make the directory for the storage
            os.makedirs(self.referenced_dir)
        
        if self.isRoot():
            # If this is a root context, let's add the directory above the root
            # to sys.path if it is needed.
            # try to import the root context; if it fails, we
            # need to add the path
            add_path = True # may set to False below
            try:
                if relurl(os.path.split(importlib.import_module(self.name).__file__)[0], self.directory) == '.':
                    add_path = False
            except:
                pass # keep add_path as True
            if add_path: # add the path to sys.path
                root_package_path = os.path.abspath(os.path.join(self.directory, '..'))
                sys.path.insert(1, root_package_path)
            # indicate whether or not we needed to add the path to sys.path
            self.addedPath = add_path             
            
            # set of context root names that are referenced
            self.referencedContextRoots = set()
            # associate the context name with the directory
            Context._setRootContextPath(name, directory)
            # map context names to paths for other known root contexts in paths.txt
            self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
            if os.path.isfile(self.pathsFilename):
                with open(self.pathsFilename) as pathsFile:
                    for pathLine in pathsFile.readlines():
                        contextName, path = pathLine.split()
                        if contextName == '.':
                            if path != directory:
                                # the directory of the context associated with 
                                # this storage object has changed.
                                self._updatePath()
                        else:
                            Context._setRootContextPath(contextName, path)
                            self.referencedContextRoots.add(contextName)
            else:
                with open(self.pathsFilename, 'w') as pathsFile:
                    # the first entry indicates the directory of this path
                    pathsFile.write('. ' + directory + '\n')

        # create the _sub_contexts_.txt file if it does not already exist
        sub_contexts_path = os.path.join(self.directory, '_sub_contexts_.txt')
        if not os.path.isfile(sub_contexts_path):
            open(sub_contexts_path, 'wt').close()
        
        self.subContextNames = []
        with open(sub_contexts_path, 'rt') as f:
            for k, line in enumerate(f.readlines()):
                self.subContextNames.append(line.strip())

        # map expression style ids to special expression kind and name
        # for the associated context (the kind is 'common', 'axiom', or 'theorem').
        self.specialExpressions = dict()
        
        # map common expression names to storage identifiers:
        self._common_expr_ids = None # read in when needed

        # Names of axioms, theorems, and common expressions that have been read in
        # and not in need of an update.
        self._axiom_names = None # store upon request for future reference
        self._theorem_names = None # store upon request for future reference
        self._common_expr_names = None # store upon request for future reference
            
        # store special expressions that have been loaded so they are
        # readily available on the next request.
        self._loadedCommonExprs = dict()
        self._loadedAxioms = dict()
        self._loadedTheorems = dict()
        
        # Map 'common', 'axiom', and 'theorem' to respective modules.
        # Base it upon the context name.
        self._specialExprModules = {kind:self.name+'.%s'%module_name for kind, module_name in Context.specialExprKindToModuleName.items()}
        
        # Reflects the contents of the 'theorem_dependency_order.txt' file
        # which lists the theorems of the context in order with other
        # theorems inserted as they are explicitly presumed.
        # Set to None to indicate it must be updated.
        self._theorem_dependency_order = self._loadTheoremDependencyOrder()
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()

    def lock(self, storageId=None):
        '''
        Place a file lock for a particular storageId directory
        or, if storageId is None, for the entire __pv_it directory
        of the context.
        '''    
        path = self.pv_it_dir
        if storageId is not None:
            path = os.path.join(path, storageId)
        while True:
            try:
                with open(os.path.join(path, 'lock'), 'w') as lock:
                    lock.write(os.getpid())
                return # lock obtain
            except IOError:
                # waiting for lock
                time.sleep(0.1)
    
    def unlock(self, storageId=None):
        '''
        Remove a file lock for a particular storageId directory
        or, if storageId is None, for the entire __pv_it directory
        of the context.
        '''
        path = self.pv_it_dir
        if storageId is not None:
            path = os.path.join(path, storageId)
        os.remove(os.path.join(path, 'lock'))
        
    def isRoot(self):
        '''
        Return True iff this ContextStorage is a "root" ContextStorage 
        (no parent directory with an __init__.py file).
        '''
        return self.rootContextStorage is self
                
    def getSubContextNames(self):
        '''
        Return the sub-context names as indicated in the _sub_contexts_.txt files.
        '''
        return self.subContextNames
        
    def setSubContextNames(self, subContextNames):
        '''
        Set the sub-context names listed in the _sub_contexts_.txt files.
        '''
        self.subContextNames = subContextNames
        with open(os.path.join(self.directory, '_sub_contexts_.txt'), 'wt') as f:
            for sub_context_name in self.subContextNames:
                f.write(sub_context_name + '\n')
                
    def appendSubContextName(self, subContextName):
        '''
        Append the sub-context name to the _sub_contexts_.txt list.
        '''
        with open(os.path.join(self.directory, '_sub_contexts_.txt'), 'a') as f:
            f.write(subContextName + '\n')
            self.subContextNames.append(subContextName)
        
    def _updatePath(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Context's.
        '''
        from .context import Context
        context_name = self.name
        # update the local paths.txt
        self._changePath('.', self.directory)
        # update the paths.txt wherever there is a mutual reference
        self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
        with open(self.pathsFilename) as pathsFile:
            for pathLine in pathsFile.readlines():
                contextName, path = pathLine.split()
                if contextName != '.':
                    Context.getContext(contextName)._storage._changePath(context_name, self.directory)
    
    def _changePath(self, movedContextName, newPath):
        '''
        Change the path of the movedContextName to the newPath.
        '''
        # read in the paths.txt
        with open(self.pathsFilename) as pathsFile:
           prevLines = pathsFile.readlines()
        # re-write the paths.txt with one of the contexts' path changed
        with open(self.pathsFilename, 'w') as pathsFile:
            for pathLine in prevLines:
                contextName, path = pathLine.split()
                if contextName == movedContextName:
                    path = newPath
                pathsFile.write(contextName + ' ' + path + '\n')

    def _includeMutualReferences(self, otherContext):
        '''
        Include a reference between context roots if they have a different root.
        '''
        otherStorage = otherContext._storage
        if self.rootContextStorage is not otherStorage.rootContextStorage:
            self.rootContextStorage._includeReference(otherStorage.rootContextStorage)
            otherStorage.rootContextStorage._includeReference(self.rootContextStorage)
                
    def _includeReference(self, otherStorage):
        '''
        Include a path reference from a root Context to another root Context,
        both in the referencedContextRoots set and in the paths.txt file. 
        '''
        otherContextName = otherStorage.name
        if otherContextName not in self.referencedContextRoots:
            with open(self.pathsFilename, 'a') as pathsFile:
                pathsFile.write(otherContextName + ' ' + otherStorage.directory + '\n')
            self.referencedContextRoots.add(otherContextName)
    
    def _loadTheoremDependencyOrder(self):
        '''
        Load the theorem dependency order that is stored in 'theorem_dependency_order.txt'.
        '''
        theorems = []
        theorems_set = set() # to check for repeats
        filename = os.path.join(self.pv_it_dir, 'theorem_dependency_order.txt')
        if not os.path.isfile(filename):
            return None # must be updated and stored to be used
        with open(filename, 'r') as f:
            for line in f:
                theorem_name = line.strip()
                theorems.append(theorem_name)
                if '.' not in theorem_name:
                    assert theorem_name not in theorems_set, "Should not have duplicated theorem names: %s"%theorem_name
                    theorems_set.add(theorem_name)
        return theorems       

    def _updateTheoremDependencyOrder(self, context_theorem_names):
        '''
        Update the information in 'theorem_dependency_order.txt' according to
        the order of the theorems in the context and the theorems that are
        presumed as indicated by their proof notebooks.
        '''
        ordered_theorems = []
        for theorem_name in context_theorem_names:
            ordered_theorems += StoredTheorem(self.context, theorem_name).explicitlyPresumedTheoremNames()
            #ordered_theorems += self.context.getTheorem(theorem_name).explicitlyPresumedTheoremNames()
            ordered_theorems.append(theorem_name)
            
        if self._theorem_dependency_order != ordered_theorems:
            filename = os.path.join(self.pv_it_dir, 'theorem_dependency_order.txt')
            with open(filename, 'w') as f:
                for theorem in ordered_theorems:
                    f.write(theorem + '\n')
        self._theorem_dependency_order = self._loadTheoremDependencyOrder()
    
    def invalidateTheoremDependencyOrder(self):
        '''
        Invalidate the theorem dependency order (both in memory and on file)
        to force it to be updated when required.
        '''
        self._theorem_dependency_order = None
        filename = os.path.join(self.pv_it_dir, 'theorem_dependency_order.txt')
        if os.path.isfile(filename):
            os.remove(filename)
        
    def setCommonExpressions(self, exprNames, exprDefinitions, clear=False):
        from proveit import Expression
        self._common_expr_names = None # force a reload
        self._common_expr_ids = dict()
        commons_filename = os.path.join(self.referenced_dir, 'commons.pv_it')
        
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
                if expr._style_id not in Expression.contexts:  
                    expr._setContext(self.context)
                self.specialExpressions[expr._style_id] = ('common', name) 
                # get the expression id to be stored on 'commons.pv_it'           
                expr_id = self._proveItStorageId(expr)
                if expr_id in old_expr_ids:
                    old_expr_ids.remove(expr_id) # same expression as before
                else:
                    # new expression not previously in the common expressions liest:
                    new_expr_ids.add(expr_id) 
                self._common_expr_ids[name] = expr_id
                f.write(name + ' ' + expr_id + '\n')
        
        # remove references to old common expressions that are no longer a common expression
        for expr_id in old_expr_ids:
            self._removeReference(expr_id, removingSpecialExpr=True) # remove reference to an old common expression
        
        # add references to new common expressions that were not preveiously a common expression
        for expr_id in new_expr_ids:
            self._addReference(expr_id) # add reference to a new common expression
        
        if clear:
            assert len(exprNames)==len(exprDefinitions), "Not expecting any expression names when 'clearing'"
            # By removing the file, we indicate that the common expressions are not defined which is
            # treated a little differently than when there are no common expressions.  In this case,
            # importing from _common_.py will generate dummy labels in order to avoid exceptions occurring
            # when the common expressions are in a non-generated state.
            os.remove(commons_filename)

    def axiomNames(self):
        if self._axiom_names is None:
            self._axiom_names = list(self._loadSpecialStatementNames('axiom'))
        return self._axiom_names

    def theoremNames(self):
        if self._theorem_names is None:
            self._theorem_names = list(self._loadSpecialStatementNames('theorem'))
        return self._theorem_names

    def commonExpressionNames(self):
        if self._common_expr_names is None:
            self._common_expr_names = list(self._loadCommonExpressionNames())
        return self._common_expr_names
            
    def setSpecialStatements(self, names, definitions, kind):
        from proveit import Expression
        from .context import Context, ContextException
        specialStatementsPath = os.path.join(self.referenced_dir, kind + 's')
        if not os.path.isdir(specialStatementsPath):
            os.makedirs(specialStatementsPath)
            
        # Force a reload of the names of this kind:
        if kind == 'axiom': self._axiom_names = None
        elif kind == 'theorem': self._theorem_names = None
        else: raise Exception("Unexpected kind: %s"%kind)
        
        # First get the previous special statement definitions to find out what has been added/changed/removed
        previousDefIds = dict()
        toRemove = []
        context_name = self.name
        for name in os.listdir(specialStatementsPath):
            try:
                with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
                    if name not in definitions:
                        # to remove special statement that no longer exists
                        toRemove.append((name, Context.getStoredStmt(context_name + '.' + name, kind)))
                    previousDefIds[name] = f.read()
            except IOError:
                raise ContextException('Corrupted __pv_it directory: %s'%self.directory)
        
        # Update the definitions, writing axiom/theorem names to axioms.txt or theorems.txt
        # in proper order.
        with open(os.path.join(self.referenced_dir, '%ss.txt'%kind), 'w') as f:            
            for name in names:
                f.write(name + '\n')
                expr = definitions[name]
                # record the special expression in this context object
                if expr._style_id not in Expression.contexts:  
                    expr._setContext(self.context)
                    self.specialExpressions[expr._style_id] = (kind, name)            
                # add the expression to the "database" via the storage object.
                expr_id = self._proveItStorageId(expr)
                if name in previousDefIds and previousDefIds[name] == expr_id:
                    continue # unchanged special statement
                storedSpecialStmt = Context.getStoredStmt(context_name + '.' + name, kind)
                if name not in previousDefIds:
                    # added special statement
                    print('Adding %s %s to %s context'%(kind, name, context_name))
                elif previousDefIds[name] != expr_id:
                    # modified special statement. remove the old one first.
                    print('Modifying %s %s in %s context'%(kind, name, context_name))
                    storedSpecialStmt.remove(keepPath=True)
                # record the axiom/theorem id (creating the directory if necessary)
                specialStatementDir = os.path.join(specialStatementsPath, name)
                if not os.path.isdir(specialStatementDir):
                    os.mkdir(specialStatementDir)
                with open(os.path.join(specialStatementDir, 'expr.pv_it'), 'w') as exprFile:
                    exprFile.write(expr_id)
                    self._addReference(expr_id)
                with open(os.path.join(specialStatementDir, 'usedBy.txt'), 'w') as exprFile:
                    pass # usedBy.txt must be created but initially empty

        # Remove the special statements that no longer exist
        for name, stmt in toRemove:
            print('Removing %s %s from %s context'%(kind, name, context_name))
            stmt.remove()
        
        if kind=='theorem':
            # update the theorem dependency order when setting the theorems
            self._updateTheoremDependencyOrder(names)
                
    def _getSpecialStatementExpr(self, kind, name):
        from proveit import Expression
        specialStatementsPath = os.path.join(self.referenced_dir, kind + 's')
        try:
            with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
                expr_id = f.read()
                start_time = time.time()
                expr = self.makeExpression(expr_id)
                if expr._style_id not in Expression.contexts:  
                    expr._setContext(self.context)
                    self.specialExpressions[expr._style_id] = (kind, name)
                return expr
        except IOError:
            raise KeyError("%s of name '%s' not found"%(kind, name))        

    def _loadCommonExpressionNames(self):
        from .context import CommonExpressions
        commons_filename = os.path.join(self.referenced_dir, 'commons.pv_it')
        context_name = self.name
        if os.path.isfile(commons_filename):
            self._common_expr_ids = dict()
            with open(commons_filename, 'r') as f:
                for line in f.readlines():
                    name, expr_id = line.split()
                    self._common_expr_ids[name] = expr_id
                    CommonExpressions.expr_id_contexts[context_name + '.' + expr_id] = self.context
                    yield name
    
    def _loadSpecialStatementNames(self, kind):
        '''
        Yield names of axioms/theorems.
        '''
        with open(os.path.join(self.referenced_dir, '%ss.txt'%kind), 'r') as f:            
            for line in f:
                yield line.strip() # name of axiom or theorem

    def getCommonExpr(self, name):
        '''
        Return the Expression of the common expression in this context
        with the given name.
        '''
        from proveit import Expression
        from .context import Context, UnsetCommonExpressions
        context_name = self.name
        if name in self._loadedCommonExprs:
            return self._loadedCommonExprs[name]
        if self._common_expr_ids is None:
            # while the names are read in, the expr id map will be generated
            list(self.commonExpressionNames())
        if self._common_expr_ids is None:
            raise UnsetCommonExpressions(context_name)
        # make the common expression for the given common expression name
        prev_context_default = Context.default
        Context.default = self.context # set the default Context in case there is a Literal
        try:
            expr = self.makeExpression(self._common_expr_ids[name])
        finally:
            Context.default = prev_context_default # reset the default Context 
        if expr._style_id not in Expression.contexts:
            expr._setContext(self.context)
        self.specialExpressions[expr._style_id] = ('common', name)
        self._loadedCommonExprs[name] = expr
        return expr
    
    def getAxiom(self, name):
        '''
        Return the Axiom of the given name in this context.
        '''
        from proveit._core_.proof import Axiom
        if name in self._loadedAxioms:
            return self._loadedAxioms[name]
        expr = self._getSpecialStatementExpr('axiom', name)
        axiom = self._loadedAxioms[name] = Axiom(expr, self.context, name)
        return axiom
            
    def getTheorem(self, name):
        '''
        Return the Theorem of the given name in this context.
        '''
        from proveit._core_.proof import Theorem
        if name in self._loadedTheorems:
            return self._loadedTheorems[name]
        expr = self._getSpecialStatementExpr('theorem', name)
        thm = self._loadedTheorems[name] = Theorem(expr, self.context, name)
        return thm
    
    def getAllPresumedTheoremNames(self, theorem_name):
        '''
        Return the set of full names of presumed theorems that are 
        directly or indirectly presumed by the theorem of the given name
        in this context.
        '''
        presumed_theorems = set()
        full_theorem_name = self.name + '.' + theorem_name
        self._allPresumedTheoremNames(theorem_name, presumed_theorems, [full_theorem_name])
        return presumed_theorems
    
    def _allPresumedTheoremNames(self, theorem_name, presumed_theorem_names, presumption_chain):
        '''
        Pass back the presumed_theorem_names, a set of full
        names of theorems, that are directly or indirectly presumed
        by the theorem of the given name in this context.  
        The presumption_chain lists the stack of recursively 
        presumed theorems to check for circular logic.
        '''
        from .context import Context
        from .proof import CircularLogicLoop
        if self._theorem_dependency_order is None:
            # The theorem dependency order is stale -- needs to be updated.
            self._updateTheoremDependencyOrder(self.theoremNames()) # update the dependency order first
        idx = self._theorem_dependency_order.index(theorem_name)
        # new presumptions in an external context as the full theorem name (with context prefix)
        new_external_presumptions = []
        
        for presumption_name in self._theorem_dependency_order[:idx]:
            if '.' in presumption_name:
                # external presumption
                new_external_presumptions.append(presumption_name)
            else:
                presumed_theorem_names.add(self.name + '.' + presumption_name) # use full name
        
        for presumption_name in new_external_presumptions:
            context_name, theorem_name = presumption_name.rsplit('.', 1)
            context = Context.getContext(context_name)
            if theorem_name not in context.theoremNames():
                raise KeyError("Theorem %s not found in context %s"%theorem_name, context.name)
            if presumption_name in presumption_chain:
                chain_index = presumption_chain.index(presumption_name)
                presumption = context.getTheorem(theorem_name)
                raise CircularLogicLoop(presumption_chain[chain_index:]+[presumption_name], presumption)
            if presumption_name not in presumed_theorem_names:
                presumed_theorem_names.add(presumption_name)
                context._storage._allPresumedTheoremNames(theorem_name, presumed_theorem_names, presumption_chain+[presumption_name])
                                                                                                              
    def retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Find the expr.png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and relative url where the png is stored as a tuple.
        '''
        from proveit import Expression
        if expr._style_id in Expression.contexts and Expression.contexts[expr._style_id] != self.context:
            return Expression.contexts[expr._style_id]._stored_png(expr, latex, configLatexToolFn)
        (context, hash_directory) = self._retrieve(expr)
        assert context==self.context, "How did the context end up different from expected??"
        # generate the latex and png file paths, from pv_it_filename and the distinction 
        latex_path = os.path.join(self.pv_it_dir, hash_directory, 'expr.latex')
        png_path = os.path.join(self.pv_it_dir, hash_directory, 'expr.png')
        # check if the latex file exists, is consistent with the given latex string, and if the png
        # file exists.
        if os.path.isfile(latex_path):
            # latex file exists.  read it ans see if it the same as the given latex string
            with open(latex_path) as latex_file:
                if latex_file.read() == latex:
                    # the latex files are the same, try to read the png file
                    if os.path.isfile(png_path):                        
                        # png file exists.  read and return the data.
                        with open(png_path, 'rb') as png_file:
                            return png_file.read(), relurl(png_path)
        # store the latex string in the latex file
        with open(latex_path, 'wb') as latex_file:
            latex_file.write(latex.encode('ascii'))
        # generate, store and return the png file
        png = self._generate_png(latex, configLatexToolFn)
        with open(png_path, 'wb') as png_file:
            png_file.write(png)
        return png, relurl(png_path)
    
    def _generate_png(self, latex, configLatexToolFn):
        '''
        Generate the png image for the given latex using the given latex
        configuration function.
        '''
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        png = latex_to_png(latex, backend='dvipng', wrap=True) # the 'matplotlib' backend can do some BAD rendering in my experience (like \lnot rendering as lnot in some contexts)
        if png is None:
            raise Exception("Unable to use 'dvipng' backend to compile LaTeX.  Be sure a LaTeX distribution is installed.")
        return png
       
    def _proveItStorageId(self, proveItObjectOrId):
        '''
        Retrieve a unique id for the Prove-It object based upon its pv_it filename from calling _retrieve.
        '''
        if isinstance(proveItObjectOrId, str):
            return proveItObjectOrId
        else:
            if isinstance(proveItObjectOrId, int):
                style_id = proveItObjectOrId # assumed to be a style id if it's an int
                (context, hash_directory) = self._proveItObjects[style_id]
            else:
                (context, hash_directory) = self._retrieve(proveItObjectOrId)
            if context != self.context:
                self._includeMutualReferences(context)
                return context.name + '.' + hash_directory
            else:
                return hash_directory
    
    def _split(self, proveItStorageId):
        '''
        Split the given storage-id into a context name and the hash directory.
        The context may be implicit (if in the same context it is referenced),
        in which case the context name will be empty.
        '''
        if '.' in proveItStorageId:
            # in a different context
            splitId = proveItStorageId.split('.')
            context_name, hash_directory = '.'.join(splitId[:-1]), splitId[-1]
            return context_name, hash_directory
        return '', proveItStorageId
            
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with the given
        storage id.
        '''
        from .context import Context
        context_name, hash_directory = self._split(proveItStorageId)
        if context_name == '':
            return os.path.join(self.pv_it_dir, hash_directory)
        else:
            pv_it_dir = Context.getContext(context_name)._storage.pv_it_dir
            return os.path.join(pv_it_dir, hash_directory)
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It object
        that is dependent upon the style.
        '''
        from proveit import Expression, KnownTruth, Proof
        prefix = None
        if isinstance(proveItObject, Expression):
            prefix = '' # No prefix for Expressions
        elif isinstance(proveItObject, KnownTruth):
            prefix = 'KnownTruth:' # prefix to indicate that it is a KnownTruth
        elif isinstance(proveItObject, Proof):
            prefix = 'Proof:' # prefix to indicate that it is a Proof
        else:
            raise NotImplementedError('Strorage only implemented for Expressions, Statements (effectively), and Proofs')
        # generate a unique representation using Prove-It object ids for this storage to
        # represent other referenced Prove-It objects 
        return prefix + proveItObject._generate_unique_rep(self._proveItStorageId)
    
    def _extractReferencedStorageIds(self, unique_rep, context_name='', 
                                     storage_ids=None):
        '''
        Given a unique representation string, returns the list of Prove-It
        storage ids of objects that are referenced.  A context_name may be
        given; if the Context is the one associated with this Storage object
        then the default may be used.
        '''
        from proveit import Expression, KnownTruth, Proof
        if storage_ids is None:
            if unique_rep[:6] == 'Proof:':
                storage_ids = Proof._extractReferencedObjIds(unique_rep[6:])
            elif unique_rep[:11] == 'KnownTruth:':
                storage_ids = KnownTruth._extractReferencedObjIds(unique_rep[11:])
            else:
                # Assumed to be an expression then
                storage_ids = Expression._extractReferencedObjIds(unique_rep)
        def relativeToExplicitPrefix(exprId, contextName):
            # If the exprId is relative to the context it is in, make the 
            # context explicit.
            if '.' in exprId: return exprId # already has an explicit context
            return contextName + '.' + exprId
        if context_name != '':
            return [relativeToExplicitPrefix(storage_id, context_name) 
                    for storage_id in storage_ids]
        return storage_ids

    def _addReference(self, proveItStorageId):
        '''
        Increment the reference count of the prove-it object with the given
        storage identifier.  The ref_count.txt file is updated with the new 
        reference count.
        '''
        from .context import CommonExpressions
        if proveItStorageId in CommonExpressions.expr_id_contexts:
            # A common expression of some Context is being referenced.
            # Keep track of this for the purpose of detecting illegal cyclic referencing of common expressions.
            CommonExpressions.referenced_contexts.add(CommonExpressions.expr_id_contexts[proveItStorageId].name)
        hash_path = self._storagePath(proveItStorageId)
        file_path = os.path.join(hash_path, 'ref_count.txt')
        with open(file_path, 'r') as f:
            # read the current reference count
            refCount = int(f.read().strip()) + 1
            # change the reference count in the file
            with open(file_path, 'w') as f2:
                f2.write(str(refCount) + '\n')

    def _getRefCount(self, proveItStorageId):
        '''
        Return the reference coult of the prove-it object with the given
        storage identifier.
        '''        
        hash_path = self._storagePath(proveItStorageId)
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            return int(f.read().strip())
           
    def _removeReference(self, proveItStorageId, removingSpecialExpr=False):
        '''
        Decrement the reference count of the prove-it object with the given
        storage identifier.  If the reference count goes down to zero, then
        the files storing this prove-it object's data will be deleted
        (and the directory if nothing else is in it).  Otherwise, the
        ref_count.txt file is simply updated with the new reference count.
        Return the new reference count and path to the hash directory.
        '''
        context_name, hash_directory = self._split(proveItStorageId)
        hash_path = self._storagePath(proveItStorageId)
        if not os.path.isdir(hash_path):
            print("WARNING: Referenced '__pv_it' path, for removal, does not exist: %s"%hash_path)
            return # not there -- skip it
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            ref_count = int(f.read().strip()) - 1
        if ref_count <= 0:
            # Reference count down to zero (or less).  Remove references to
            # referenced objects and then delete this prove-it object from
            # storage and everything associated with it.
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                rep = f.read()
            for objId in self._extractReferencedStorageIds(rep, context_name):
                self._removeReference(objId)
            # remove the entire directory storing this prove-it object
            self._erase_hash_directory(hash_path)
        else:
            # change the reference count in the file
            with open(os.path.join(hash_path, 'ref_count.txt'), 'w') as f:
                f.write(str(ref_count)+'\n')
            if removingSpecialExpr:
                # there are other references to the expression, but it is no
                # longer a special expression (presumably)
                name_path = os.path.join(hash_path, 'name.txt')
                if os.path.isfile(name_path):
                    os.remove(name_path)
                kind_path = os.path.join(hash_path, 'kind.txt')
                if os.path.isfile(kind_path):
                    os.remove(kind_path)    
    
    def _erase_hash_directory(self, hash_path):
        '''
        Remove the entire directory storing this prove-it object.
        '''
        for filename in os.listdir(hash_path):
            path = os.path.join(hash_path, filename)
            if os.path.isdir(path):
                for sub_filename in os.listdir(path):
                    os.remove(os.path.join(path, sub_filename))
                os.rmdir(path)
            else:
                os.remove(path)
        os.rmdir(hash_path)
        
    
    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the (context, hash_directory)
        pair, where the hash_directory is the directory name (within the context's
        __pv_it directory) based upon a hash of the unique representation.
        '''
        from proveit import Expression
        if proveItObject._style_id in self._proveItObjects:
            return self._proveItObjects[proveItObject._style_id]
        if isinstance(proveItObject, Expression):
            expr = proveItObject
            if expr._style_id in Expression.contexts and Expression.contexts[expr._style_id] != self.context:
                # stored in a different context
                return Expression.contexts[expr._style_id]._storage._retrieve(proveItObject)
        elif hasattr(proveItObject, 'context') and proveItObject.context != self.context:
            # stored in a different context
            return proveItObject.context._storage._retrieve(proveItObject)
        pv_it_dir = self.pv_it_dir
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep.encode('utf-8')).hexdigest()
        if not os.path.exists(pv_it_dir):
            os.mkdir(pv_it_dir)
        hash_path = os.path.join(pv_it_dir, rep_hash)
        # append the hash value with an index, avoiding collisions (that should
        # be astronomically rare, but let's not risk it).
        index = 0
        while os.path.exists(hash_path + str(index)):
            indexed_hash_path = hash_path + str(index)
            unique_rep_filename = os.path.join(indexed_hash_path, 'unique_rep.pv_it')
            if not os.path.isfile(unique_rep_filename):
                # folder does not contain a unique_rep.pv_it file;
                # assume it was not erased properly a previous time 
                # and try to remove it again.
                self._erase_hash_directory(indexed_hash_path)
                break
            with open(unique_rep_filename, 'r') as f:
                rep = f.read()
                if rep != unique_rep:
                    # there is a hashing collision (this should be astronically rare, but we'll make sure just in case)
                    index += 1 # increment the index and try again
                    continue
            # found a match; it is already in storage
            # remember this for next time
            result = (self.context, rep_hash + str(index))
            self._proveItObjects[proveItObject._style_id] = result
            return result
        indexed_hash_path = hash_path + str(index)
        # store the unique representation in the appropriate file
        os.mkdir(indexed_hash_path)
        with open(os.path.join(indexed_hash_path, 'unique_rep.pv_it'), 'w') as f:
            f.write(unique_rep) 
        # write a reference count of zero (initially)
        with open(os.path.join(indexed_hash_path, 'ref_count.txt'), 'w') as f:
            f.write("0\n") 
        # increment reference counts of the referenced objects
        for objId in self._extractReferencedStorageIds(unique_rep):
            self._addReference(objId)
        # remember this for next time
        result = (self.context, rep_hash + str(index))
        self._proveItObjects[proveItObject._style_id] = result
        return result
    
    def expressionNotebook(self, expr, unofficialNameKindContext=None):
        '''
        Return the path of the expression notebook, creating it if it
        does not already exist.  If 'unofficialNameKindContext' is provided,
        it should be the (name, kind, context) for a special expression
        that is not-yet-official (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        import proveit
        from proveit import Expression, expressionDepth
        from .context import Context
        
        if not isinstance(expr, Expression):
            raise ValueError("'expr' should be an Expression object")

        context, hash_directory = self._retrieve(expr)
        if context != self.context:
            return context._storage.expressionNotebook(expr)
        
        # If the expression is a special expression (common expression, axiom,
        # or theorem) mark the name in 'name.txt'.
        # That way we will know whether or not the notebook needs to be
        # re-written (if we did not know it was a special expression before).
        try:
            expr_address = self.context.specialExprAddress(expr)
            special_name = expr_address[-1].split('.')[0] # strip off ".expr"
        except KeyError:
            expr_address = None
        needs_rewriting = False
        if expr_address is not None:
            special_expr_name_filename = os.path.join(self.pv_it_dir, hash_directory, 'name.txt')
            if not os.path.isfile(special_expr_name_filename):
                needs_rewriting = True
                with open(special_expr_name_filename, 'w') as nameFile:
                    nameFile.write(special_name)
                special_expr_kind_filename = os.path.join(self.pv_it_dir, hash_directory, 'kind.txt')
                with open(special_expr_kind_filename, 'w') as kindFile:
                    kindFile.write(expr_address[0])                
        filename = os.path.join(self.pv_it_dir, hash_directory, 'expr.ipynb')
        if not needs_rewriting and os.path.isfile(filename):
            return relurl(filename) # return the existing expression notebook file
        elif os.path.isfile(filename):
            # Store the original version as orig_expr.ipynb.  It will be
            # resurrected if the expression is no longer "special" but still used.
            orig_notebook_filename = os.path.join(self.pv_it_dir, hash_directory, 'orig_expr.ipynb')
            if os.path.isfile(orig_notebook_filename):
                os.remove(orig_notebook_filename) # remove an old one first
            os.rename(filename, orig_notebook_filename)
            print("%s expression notebook is being updated"%special_name)
        
        expr_classes_and_constructors = set()
        unnamed_subexpr_occurences = dict()
        named_subexpr_addresses = dict()
        # maps each class name or special expression name to a list of objects being represented; that
        # way we will know whether we can use the abbreviated name or full address.
        named_items = dict() 
        self._exprBuildingPrerequisites(expr, expr_classes_and_constructors, unnamed_subexpr_occurences, named_subexpr_addresses, named_items, isSubExpr=False)
        # find sub-expression style ids that are used multiple times, these ones will be assigned to a variable
        multiuse_subexprs = [sub_expr for sub_expr, count in unnamed_subexpr_occurences.items() if count > 1]
        # sort the multi-use sub-expressions so that the shallower ones come first
        multiuse_subexprs = sorted(multiuse_subexprs, key = lambda expr_and_styleid : expressionDepth(expr_and_styleid[0]))
        
        # map modules to lists of objects to import from the module
        from_imports = dict()
        # set of modules to import directly
        direct_imports = set()
        # map from expression classes or expression style ids to their names (abbreviated if there is no
        # ambiguity, otherwise using the full address).
        item_names = dict() 
        
        # populate from_imports, direct_imports, and item_names
        for expr_class, constructor in expr_classes_and_constructors:
            class_name = expr_class.__name__
            module_name = self._moduleAbbreviatedName(expr_class.__module__, class_name)
            is_unique = (len(named_items[class_name]) == 1)
            if is_unique:
                from_imports.setdefault(module_name, []).append(constructor)
                item_names[expr_class] = class_name
            else:
                direct_imports.add(module_name)
                item_names[expr_class] = module_name+'.'+constructor
        for namedExprAndStyleId, namedExprAddress in named_subexpr_addresses.items():
            if isinstance(namedExprAddress[0], str):
                # Must be a special expression (axiom, theorem, 
                module_name = namedExprAddress[0] # or common expression)
                item_names[namedExprAndStyleId] = itemName = namedExprAddress[-1]
                 # Split off '.expr' part if it is a Theorem or Axiom 
                 # KnownTruth
                objName = itemName.split('.')[0]
                module_name = self._moduleAbbreviatedName(module_name, objName)
                is_unique = (len(named_items[itemName]) == 1)
                from_imports.setdefault(module_name, []).append(objName)
            else:
                # Expression must be an attribute of a class (e.g., '_operator_')
                item_names[namedExprAndStyleId] = item_names[namedExprAddress[0]] + '.' + namedExprAddress[1]
                
        # see if we need to add anything to the sys.path
        needs_root_path = False # needs the root of this context added
        needs_local_path = False # needs the local path added
        # first, see if we even need to import a module with the same root as our context
        root_context = self.rootContextStorage.context
        context_root_name = root_context.name
        for module_name in itertools.chain(direct_imports, list(from_imports.keys())):
            if module_name.split('.')[0] == context_root_name:
                # If we needed to add a path to sys.path for the directory above the root context,
                # we'll need to do that explicitly in our expression notebook.
                needs_root_path = root_context._storage.addedPath
                break
            else:
                module = importlib.import_module(module_name)
                if module.__package__ == '':
                    needs_local_path = True
        
        # generate the imports that we need (appending to sys.path if necessary).
        import_stmts = []
        if needs_root_path or needs_local_path:
            # add to the sys path
            import_stmts = ['import sys']
            rel_paths = set()
            if needs_local_path:
                # go up 2 levels, where the local directory is
                rel_paths.add(relurl('.', start=os.path.join(self.pv_it_dir, hash_directory)))
            if needs_root_path:
                # go up enough levels to the context root;
                # 2 levels to get out of the '__pv_it' folder and at least
                # 1 more to get above the root context.
                rel_paths.add(os.path.join(*(['..']*(self.name.count('.')+3))))
            for rel_path in rel_paths:
                import_stmts.append(json.dumps('sys.path.insert(1, "%s")'%rel_path).strip('"'))
        # direct import statements
        import_stmts += ['import %s'%module_name for module_name in sorted(direct_imports)]
        # from import statements
        import_stmts += ['from %s import '%module_name + ', '.join(sorted(from_imports[module_name])) for module_name in sorted(from_imports.keys())]
        # code to perform the required imports
        import_code = '\\n",\n\t"'.join(import_stmts)
        
        # generate the code for building the expression
        expr_code = ''
        idx = 0
        for sub_expr_and_style_id in multiuse_subexprs:
            sub_expr, sub_expr_style_id = sub_expr_and_style_id
            if hasattr(sub_expr, 'context') and sub_expr.context is not None:
                continue # this expression is pulled from a context and does not need to be built
            idx += 1
            sub_expr_name = 'subExpr%d'%idx
            expr_code += sub_expr_name + ' = ' + json.dumps(self._exprBuildingCode(sub_expr, item_names, isSubExpr=True)).strip('"') + '\\n",\n\t"'
            item_names[sub_expr_and_style_id] = sub_expr_name
        expr_code += 'expr = ' + json.dumps(self._exprBuildingCode(expr, item_names, isSubExpr=False)).strip('"')
        
        # link to documentation for the expression's type
        proveit_path = os.path.split(proveit.__file__)[0]
        doc_root = os.path.join(proveit_path, '..', '..', 'doc', 'html', 'api')
        class_name = expr.__class__.__name__
        module_name = self._moduleAbbreviatedName(expr.__class__.__module__, class_name)
        doc_file = module_name + '.' + class_name + '.html'
        type_link = relurl(os.path.join(doc_root,doc_file), start=os.path.join(self.pv_it_dir, hash_directory))
        
        # read the template and change the contexts as appropriate
        if unofficialNameKindContext is not None:
            template_name = '_unofficial_special_expr_template_.ipynb'
            name, kind, context = unofficialNameKindContext
        elif expr_address is not None:
            kind, name = self.context.specialExpr(expr)
            if kind=='common':
                template_name = '_common_expr_template_.ipynb'
            else:
                template_name = '_special_expr_template_.ipynb'
        else:
            template_name = '_expr_template_.ipynb'
        with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
            nb = template.read()
            if template_name != '_special_expr_template_.ipynb' and template_name != '_common_expr_template_.ipynb':
                nb = nb.replace('#EXPR#', expr_code)
            nb = nb.replace('#IMPORTS#', import_code)
            nb = nb.replace('#CONTEXT#', context.name)
            nb = nb.replace('#TYPE#',class_name)
            nb = nb.replace('#TYPE_LINK#', type_link.replace('\\', '\\\\'))
            if unofficialNameKindContext is not None or expr_address is not None:
                kind_str = kind[0].upper() + kind[1:]
                if kind == 'common': kind_str = 'Common Expression'
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = '/'.join(['..', '..', Context.specialExprKindToModuleName[kind] + '.ipynb'])
                nb = nb.replace('#SPECIAL_EXPR_LINK#', json.dumps(special_expr_link + '#' + name).strip('"'))
        # write the expression notebook
        with open(filename, 'w') as expr_file:
            expr_file.write(nb)
        
        # if this is a special expression also generate the dependencies notebook if it does not yet exist
        if template_name == '_special_expr_template_.ipynb':
            dependencies_filename = os.path.join(self.pv_it_dir, hash_directory, 'dependencies.ipynb')
            # Even if the dependencies file exists, write over it since the expression notebook
            # was rewritten.  This will guarantee the file is overwritten if it needs to be (the
            # name or kind of the special expression changes) and not overwritten if the expression
            # notebook was allowed to remain unchanged.
            with open(os.path.join(proveit_path, '..', '_dependencies_template_.ipynb'), 'r') as template:
                nb = template.read()
                nb = nb.replace('#IMPORTS#', import_code)
                nb = nb.replace('#CONTEXT#', context.name)
                nb = nb.replace('#TYPE#', class_name)
                nb = nb.replace('#TYPE_LINK#', type_link.replace('\\', '\\\\'))
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                nb = nb.replace('#SPECIAL_EXPR_LINK#', json.dumps(special_expr_link + '#' + name).strip('"'))  
                if kind_str == 'Theorem':
                    see_proof_str = '***see <a class=\\"ProveItLink\\" href=\\"../../_proofs_/%s.ipynb\\">proof</a>***'%name
                else: see_proof_str = ''
                nb = nb.replace('#SEE_PROOF#', see_proof_str)
            with open(dependencies_filename, 'w') as dependencies_file:
                dependencies_file.write(nb)
            
        return relurl(filename) # return the relative url to the new proof file
        
    def _exprBuildingPrerequisites(self, expr, exprClassesAndConstructors, unnamedSubExprOccurences, namedSubExprAddresses, namedItems, isSubExpr=True):
        '''
        Given an Expression object (expr), visit all sub-expressions and obtain the set of 
        represented Expression classes (exprClasses), the count for 'unnamed' sub-Expression
        occurances (unnamedSubExprOccurances as an Expression:int dictionary),
        the 'address' of all named sub-Expressions [namedSubExprAddresses as an
        Expression:expression-address dictionary], and the Expression(s)/class(es) corresponding
        to each named item (namedItems as a name:set dictionary).  The expression-address
        is in the form (module, name) for special-expressions or (Expression class, '_operator_')
        for a Literal operator.  When there are muliple items with the same name, full names 
        must be used instead of abbreviations.
        '''
        from proveit import Operation, Expression, ExprTuple, NamedExprs, ExprArray
        
        if expr in Operation.operationClassOfOperator:
            # the expression is an '_operator_' of an Operation class
            operationClass = Operation.operationClassOfOperator[expr]
            exprClassesAndConstructors.add((operationClass, operationClass.__name__))
            namedItems.setdefault(operationClass.__name__, set()).add(operationClass)
            namedSubExprAddresses[(operationClass._operator_, operationClass._operator_._style_id)] = (operationClass, '_operator_')
            return
            
        if expr._style_id in Expression.contexts:
            # expr may be a special expression from a context
            try:
                # if it is a special expression in a context, 
                # we want to be able to address it as such.
                exprAddress = Expression.contexts[expr._style_id].specialExprAddress(expr)
                namedSubExprAddresses[(expr, expr._style_id)] = exprAddress[1:]
                namedItems.setdefault(exprAddress[-1], set()).add(expr)
                return
            except KeyError:
                pass
        
        # add to the unnamed sub-expression count
        unnamedSubExprOccurences[(expr, expr._style_id)] = unnamedSubExprOccurences.get((expr, expr._style_id), 0) + 1
        if unnamedSubExprOccurences[(expr, expr._style_id)] > 1:
            return # already visited this -- no need to reprocess it
        
        if not isSubExpr or expr.__class__ not in (ExprTuple, NamedExprs, ExprArray): 
            # add expr's class to exprClass and named items (unless it is a basic Composite sub-Expression
            # in which case we'll use a python list or dictionary to represent the composite expression).
            exprClassesAndConstructors.add((expr.__class__, expr.remakeConstructor()))
            namedItems.setdefault(expr.__class__.__name__, set()).add(expr.__class__)
                                
        # recurse over the expression build arguments (e.g., the sub-Expressions
        for arg in expr.remakeArguments():
            try:
                if isinstance(arg[0], str):
                    argname, arg = arg # splits into a name, argument pair
            except:
                pass
            if not isinstance(arg, Expression) and not isinstance(arg, str) and not isinstance(arg, int):
                raise TypeError("The arguments of %s.remakeArguments() should be Expressions or strings or integers: %s instead." %(str(expr.__class__), str(arg.__class__)))
            if isinstance(arg, Expression):
                subExpr = arg
                self._exprBuildingPrerequisites(subExpr, exprClassesAndConstructors, unnamedSubExprOccurences, namedSubExprAddresses, namedItems)
        
    def _moduleAbbreviatedName(self, moduleName, objName):
        '''
        Return the abbreviated module name for the given object based upon
        the convention that packages will import objects within that package
        that should be visible externally.  Specifically, this successively
        checks parent packages to see of the object is defined there with
        the same name.  For example, 
        proveit.logic.boolean.conjunction.and_op will be abbreviated
        to proveit.logic for the 'And' class.
        '''
        module = importlib.import_module(moduleName)
            
        if not os.path.isabs(module.__file__):
            # convert a relative path to a path starting from the context root
            abs_module_name = self.name + '.' + moduleName
            if abs_module_name not in sys.modules:
                return moduleName # just use the relative path
        split_module_name = moduleName.split('.')
        while len(split_module_name) > 1:
            cur_module = sys.modules['.'.join(split_module_name)]
            parent_module = sys.modules['.'.join(split_module_name[:-1])]
            if not hasattr(parent_module, objName): break
            if getattr(cur_module, objName) != getattr(parent_module, objName):
                # reload the parent module and try again
                imp.reload(parent_module)
                if getattr(cur_module, objName) != getattr(parent_module, objName):
                    break
            split_module_name = split_module_name[:-1]
        return '.'.join(split_module_name)
    
    def _exprBuildingCode(self, expr, itemNames, isSubExpr=True):
        from proveit import Expression, Composite, ExprTuple, NamedExprs, ExprArray
                
        if expr is None: return 'None' # special 'None' case
        
        if (expr, expr._style_id) in itemNames:
            # the expression is simply a named item
            return itemNames[(expr, expr._style_id)]
        
        def argToString(arg):
            if isinstance(arg, str): 
                return arg # just a single string
            if isinstance(arg, int):
                return str(arg) # ineger to convert to a string
            if isinstance(arg, Expression):
                # convert a sub-Expression to a string, 
                # either a variable name or code to construct the sub-expression:
                return self._exprBuildingCode(arg, itemNames)
            # see of we can split arg into a (name, value) pair
            try:
                name, val = arg
                if isinstance(name, str):
                    return name + ' = ' + argToString(val)
            except:
                pass
            # the final possibility is that we need a list of expressions (i.e., parameters of a Lambda expression)
            return '[' + ', '.join(argToString(argItem) for argItem in arg) + ']' 
        
        def get_constructor():
            constructor = expr.remakeConstructor() # usually the class name to call the __init__, but not always
            full_class_name = itemNames[expr.__class__] # may include the module at the front
            if '.' in full_class_name:
                # prepend the constructor with the module -- assume it is in the same module as the class
                constructor = '.'.join(full_class_name.split('.')[:-1]) + constructor
            return constructor
        if isinstance(expr, NamedExprs):
            # convert to (name, value) tuple form
            argStr = ', '.join('(' + argToString(arg).replace(' = ', ',') + ')' for arg in expr.remakeArguments())                
        else:
            argStr = ', '.join(argToString(arg) for arg in expr.remakeArguments())                
        withStyleCalls = '.'.join(expr.remakeWithStyleCalls())
        if len(withStyleCalls)>0: withStyleCalls = '.' + withStyleCalls

        if isinstance(expr, Composite):
            if isinstance(expr, ExprTuple):
                compositeStr = argStr
            elif isinstance(expr, ExprArray):
                compositeStr = '{' + argStr.replace(' = ', ':') + '}'                
            else:
                assert isinstance(expr, NamedExprs)
                compositeStr = '[' + argStr.replace(' = ', ':') + ']' # list of (name, value) tuples                
            if isSubExpr and expr.__class__ in (ExprTuple, NamedExprs, ExprArray): 
                # It is a sub-Expression and a standard composite class.
                # Just pass it in as an implicit composite expression (a list or dictionary).
                # The constructor should be equipped to handle it appropriately.
                return '[' + compositeStr + ']' if expr.__class__==ExprTuple else compositeStr
            else:
                return get_constructor() + '(' + compositeStr + ')' + withStyleCalls
        else:
            return get_constructor() + '(' + argStr + ')' + withStyleCalls
    
    def proofNotebook(self, proof):
        '''
        Return the url to a proof notebook for the given stored proof.
        Create the notebook if necessary.
        '''
        import proveit
        (context, hash_directory) = self._retrieve(proof)
        pv_it_dir = context._storage.pv_it_dir
        filename = os.path.join(pv_it_dir, hash_directory, 'proof.ipynb')
        proveit_path = os.path.split(proveit.__file__)[0]
        template_filename = os.path.join(proveit_path, '..', 
                                         '_proof_template_.ipynb')
        if not os.path.isfile(filename):
            # Copy the template.  Nothing needs to be edited for these.
            shutil.copyfile(template_filename, filename)
        return relurl(filename)
    
    def thmProofNotebook(self, theorem_name, expr):
        '''
        Return the relative url to the proof notebook, creating it if it does not
        already exist.
        '''
        context, hash_directory = self._retrieve(expr)
        proofs_path = os.path.join(self.directory, '_proofs_')
        filename = os.path.join(proofs_path, '%s.ipynb'%theorem_name)
        if os.path.isfile(filename):
            # Check the theorem name and make sure the capitalization
            # is the same.  If not, revise it appropriately.
            existing_theorem_name = self._proofNotebookTheoremName(filename)
            if existing_theorem_name is None:
                # The format is not correct; stash this one and generate a new one.
                self._stashNotebook(filename)
            else:
                if existing_theorem_name != theorem_name:
                    # update with the new capitalization
                    with open(filename, 'r') as proof_notebook:
                        nb = proof_notebook.read()
                    nb = nb.replace(existing_theorem_name, theorem_name)
                    # remove the file before creating again to force the new
                    # capitolization (e.g., in Windows where capitolization 
                    # can be flexible)
                    os.remove(filename) 
                    with open(filename, 'w') as proof_notebook:
                        proof_notebook.write(nb)
                return relurl(filename)
        if not os.path.isdir(proofs_path):
            # make the directory for the _proofs_
            os.makedirs(proofs_path)            
        nb = self._generateGenericThmProofNotebook(theorem_name)
        # write the proof file
        with open(filename, 'w') as proof_notebook:
            proof_notebook.write(nb)
        return relurl(filename) # return the new proof file
    
    def _generateGenericThmProofNotebook(self, theorem_name):
        '''
        Given a theorem name and hash directory, generate the generic start
        of a proof notebook using the template.
        '''
        import proveit
        # read the template and change the contexts as appropriate
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_theorem_proof_template_.ipynb'), 'r') as template:
            nb = template.read()
            nb = nb.replace('#THEOREM_NAME#', theorem_name)
            context_links = self.context.links(os.path.join(self.directory, '_proofs_'))
            nb = nb.replace('#CONTEXT#', context_links)
        return nb
    
    def _proofNotebookTheoremName(self, filename):
        '''
        Return the theorem name extracted from the proof notebook.
        '''
        with open(filename, 'r') as proof_notebook:
            nb = proof_notebook.read()
            # the theorem name should come after "_theorems_.ipynb#" in the notebook
            match =  re.search(r'_theorems_\.ipynb\#([_a-zA-Z]\w*)', nb)
            if match is None: return None
            return match.groups()[0]
            
    def stashExtraneousThmProofNotebooks(self, theorem_names):
        '''
        For any proof notebooks for theorem names not included in the given 
        theorem_names, stash them or remove them if they are generic notebooks.
        '''
        proofs_path = os.path.join(self.directory, '_proofs_')
        if not os.path.isdir(proofs_path):
            return # nothing to stash
        for filename in os.listdir(proofs_path):
            if os.path.splitext(filename)[-1] != '.ipynb':
                continue # just concerned with notebooks
                
            # see if this is a proof notebook that should be kept
            if filename[:-len('.ipynb')] in theorem_names:
                continue # this one is a keeper
                
            filename = os.path.join(proofs_path, filename)
            if os.path.isdir(filename): continue # skip directories
            
            if "~stashed~" in filename:
                continue # already a stashed notebook
            
            remove_file = False # may be set to True below if it is a generic notebook
            
            # next, let's see if this is a generic notebook by extracting
            # its info, building the generic version, and comparing.
            theorem_name = self._proofNotebookTheoremName(filename)
            if theorem_name is not None:
                generic_version = self._generateGenericThmProofNotebook(theorem_name)        
                with open(filename, 'r') as notebook:
                    if generic_version == notebook.read():
                        remove_file = True # just remove it, it is generic
            
            if remove_file:
                os.remove(filename)
            else:
                self._stashNotebook(filename)
    
    def _stashNotebook(self, filename):
        '''
        Stash a notebook to a "~stashed~#" file using a '#' (number)
        that has not been used yet.
        '''
        num = 1
        filename_base = filename[:-len('.ipynb')]
        while os.path.isfile(filename_base + "~stashed~%d.ipynb"%num):
            num += 1
        new_filename = filename_base + "~stashed~%d.ipynb"%num
        print("Stashing %s to %s in case it is needed."%(relurl(filename), relurl(new_filename)))
        os.rename(filename, new_filename)
                
    def makeExpression(self, exprId):
        '''
        Return the Expression object that is represented in storage by
        the given expression id.
        '''
        import importlib
        from proveit import Expression, Lambda
        expr_class_map = dict() # map expression class strings to Expression class objects
        def importFn(exprClassStr):
            split_expr_class = exprClassStr.split('.')
            module = importlib.import_module('.'.join(split_expr_class[:-1]))
            expr_class_map[exprClassStr] = getattr(module, split_expr_class[-1])
        def exprBuilderFn(exprClassStr, exprInfo, styles, subExpressions, genericExpr,
                          context):
            expr_class = expr_class_map[exprClassStr]
            if issubclass(expr_class, Lambda):
                # For efficiency, make the Lambda expression with its generic
                # version known to avoid needing to generate it via relabeling.
                expr = expr_class._make(exprInfo, styles, subExpressions, 
                                        genericExpr)
            else:
                expr = expr_class._make(exprInfo, styles, subExpressions)
            if context is not None and expr._style_id not in Expression.contexts:
                expr._setContext(context)
                # see if it is a special expression with an addressable name.
                # if so, note the address for future reference (in self.specialExpressions)
                (context, hash_directory) = self._retrieve(expr)
                pv_it_dir = context._storage.pv_it_dir
                special_expr_name_filename = os.path.join(pv_it_dir, hash_directory, 'name.txt')
                special_expr_kind_filename = os.path.join(pv_it_dir, hash_directory, 'kind.txt')
                if os.path.isfile(special_expr_name_filename):
                    with open(special_expr_name_filename, 'r') as nameFile:
                        name = nameFile.read()
                    with open(special_expr_kind_filename, 'r') as kindFile:
                        kind = kindFile.read()
                    context._storage.specialExpressions[expr._style_id] = (kind, name)                    
            return expr
        return self._makeExpression(exprId, importFn, exprBuilderFn)
        
    def _makeExpression(self, exprId, importFn, exprBuilderFn):
        '''
        Helper method for makeExpression
        '''
        from proveit import Expression
        from ._dependency_graph import orderedDependencyNodes
        from .context import Context
        expr_class_strs = dict() # map expr-ids to lists of Expression class string representations
        expr_class_rel_strs = dict() # relative paths of Expression classes that are local
        core_info_map = dict() # map expr-ids to core information
        styles_map = dict() # map expr-ids to style information
        generic_id_map = dict() # map expr-ids to the generic version
        sub_expr_ids_map = dict() # map expr-ids to list of sub-expression ids
        context_map = dict() # map expr-ids to a Context 
        master_expr_id = exprId
        try:
            local_context_name = Context().name
        except:
            local_context_name = None
                
        def getDependentExprIds(exprId):
            '''
            Given an expression id, yield the ids of all of its sub-expressions
            as well as the id of the generic version of the expression if it
            is not the generic version.
            '''
            context_name, hash_directory = self._split(exprId)
            if context_name != '': context_map[exprId] = Context.getContext(context_name)
            hash_path = self._storagePath(exprId)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # Extract the unique representation from the pv_it file.
                unique_rep = f.read()
                # Parse the unique_rep to get the expression information.
                expr_class_str, core_info, style_dict, sub_expr_refs, generic_ref \
                    = Expression._parse_unique_rep(unique_rep)
                if local_context_name is not None and expr_class_str.find(local_context_name) == 0:
                    # import locally if necessary
                    expr_class_rel_strs[exprId] = expr_class_str[len(local_context_name)+1:]                
                expr_class_strs[exprId] = expr_class_str
                # extract the Expression "core information" from the unique representation
                core_info_map[exprId] = core_info
                styles_map[exprId] = style_dict
                if generic_ref != '' and generic_ref != '.':
                    dependent_refs = [generic_ref] + sub_expr_refs
                else:
                    dependent_refs = sub_expr_refs
                dependent_ids = \
                    self._extractReferencedStorageIds(unique_rep, context_name, 
                                                      storage_ids=dependent_refs)
                if generic_ref == '.':
                    # '.' denotes that this is a "generic" expression itself.
                    generic_id_map[exprId] = '.'
                    sub_expr_ids_map[exprId] = dependent_ids
                elif generic_ref == '':
                    sub_expr_ids_map[exprId] = dependent_ids
                else:
                    generic_id_map[exprId] = dependent_ids[0]
                    sub_expr_ids_map[exprId] = dependent_ids[1:]
                return dependent_ids
        
        expr_ids = orderedDependencyNodes(exprId, getDependentExprIds)
        for expr_id in reversed(expr_ids):
            if expr_id in expr_class_rel_strs:
                # there exists a relative path
                try:
                    # First try the absolute path; that is preferred for
                    # consistency sake (we want different imports of something
                    # to be regarded as the same)
                    importFn(expr_class_strs[expr_id])
                except:
                    # If importing the absolute path fails, maybe the relative
                    # path will work.  This is needed to resolve, for example,
                    # the issue that the proveit.logic package imports from
                    # proveit.logic.boolean._common_ but we need to be able
                    # to execute proveit.logic.boolean._common_.ipynb in
                    # the first place which requires imports within 
                    # proveit.logic.boolean.  The solution is to use relative
                    # imports when executing proveit.logic.boolean._common_.ipynb
                    # the first time but afterwards use absolute paths. 
                    importFn(expr_class_rel_strs[expr_id])
                    # use the relative path
                    expr_class_strs[expr_id] = expr_class_rel_strs[expr_id]
            else:
                # there does not exist a relative path; 
                # the absolute path is the only option.
                importFn(expr_class_strs[expr_id])
        built_expr_map = dict() # map expr-ids to "built" expressions (whatever exprBuilderFn returns)
        for expr_id in reversed(expr_ids):
            sub_expressions =  [built_expr_map[sub_expr_id] for sub_expr_id in sub_expr_ids_map[expr_id]]
            context = context_map[expr_id] if expr_id in context_map else None
            if expr_id in generic_id_map:
                generic_id = generic_id_map[expr_id]
                if generic_id == '.': generic_expr = '.'
                else: generic_expr = built_expr_map[generic_id]
            else: generic_expr = None
            expr = exprBuilderFn(expr_class_strs[expr_id], core_info_map[expr_id], 
                                 styles_map[expr_id], sub_expressions, 
                                 generic_expr, context)
            built_expr_map[expr_id] = expr
        return built_expr_map[master_expr_id]        
    
    def makeKnownTruth(self, truthId):
        '''
        Return the KnownTruth object that is represented in storage by
        the given KnownTruth id.
        '''
        from proveit._core_.known_truth import KnownTruth
        context_name, _ = self._split(truthId)
        hash_path = self._storagePath(truthId)
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        exprids = self._extractReferencedStorageIds(unique_rep, context_name)
        truth_expr_id = self.makeExpression(exprids[0])
        assumptions = [self.makeExpression(exprid) for exprid in exprids[1:]]
        return KnownTruth(truth_expr_id, assumptions)
        
    def makeShowProof(self, proof_id):
        '''
        Return the _ShowProof object that mocks up the proof 
        represented in storage by the given proof id for just
        the purposes of displaying the proof.
        '''
        from proveit._core_.proof import Proof
        from proveit._core_.context import Context
        context_name, hash_directory = self._split(proof_id)
        if context_name=='':
            context = self.context
        else:
            context = Context.getContext(context_name)
        hash_path = self._storagePath(proof_id)        
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        proof_id = context.name + '.' + hash_directory # full storage id
        self._proveItObjects[proof_id] = (context, hash_directory)   
        return Proof._showProof(context, proof_id, unique_rep)
        
    def recordCommonExprDependencies(self):
        '''
        Record the context names of any reference common expressions in storage
        while creating the common expressions for this context
        (for the purposes of checking for illegal mutual dependencies).
        '''
        from .context import CommonExpressions
        contextNames = CommonExpressions.referenced_contexts
        contextNames = set(contextNames)
        contextNames.discard(self.name) # exclude the source context
        if contextNames == self.storedCommonExprDependencies():
            return # unchanged
        referenced_commons_filename = os.path.join(self.referenced_dir, 'commons_dependencies.txt')
        with open(referenced_commons_filename, 'w') as f:
            for context_name in contextNames:
                f.write(context_name + '\n')

    def storedCommonExprDependencies(self):
        '''
        Return the stored set of context names of common expressions
        referenced by the common expression notebook of this context.
        '''
        referenced_commons_filename = os.path.join(self.referenced_dir, 'commons_dependencies.txt')
        if os.path.isfile(referenced_commons_filename):
            with open(referenced_commons_filename, 'r') as f:
                return {line.strip() for line in f.readlines()}
        return set() # empty set by default
        
    def cyclicallyReferencedCommonExprContext(self):
        '''
        Check for illegal cyclic dependencies of common expression notebooks.
        If there is one, return the name; otherwise return None.
        '''        
        from .context import Context, CommonExpressions
        contextNames = CommonExpressions.referenced_contexts
        referencing_contexts = {contextName:self.context for contextName in contextNames if contextName != self.name}
        while len(referencing_contexts) > 0:
            contextName, referencing_context = referencing_contexts.popitem()
            context = Context.getContext(contextName)
            if context == self.context:
                # a directly or indirectly referenced context refers back to the referencing source
                return referencing_context # cycle found; report context with a common expression referencing the source
            # extend with indirect references
            new_context_names = context.storedCommonExprDependencies()
            for new_context_name in new_context_names:
                if new_context_name not in referencing_contexts:
                    # add an indirect reference
                    referencing_contexts[new_context_name] = context
        return None
    
    def referenceHyperlinkedObjects(self, name, clear=False):
        '''
        Reference displayed expressions and proofs of displayed
        KnownTruths recorded under the given name
        in the __pv_it directory.  If the same name is reused,
        any expressions that are not displayed this time that
        were displayed last time will be unreferenced.
        If clear is True, remove all of the references and the
        file that stores these references.
        '''
        from proveit import Expression, KnownTruth
        
        reference_file = os.path.join(self.referenced_dir, name + '_hyperlinked.pv_it')
        
        # read in previous "displayed" expressions
        previous = set()
        if os.path.isfile(reference_file):
            with open(reference_file, 'r') as f:
                for line in f.readlines():
                    previous.add(line.strip())
        
        # Grab the current "displayed" expressions and hyperlinked
        # proofs:
        current = {self._proveItStorageId(expr) for style_id, expr 
                   in Expression.displayed_expression_styles}
        current.update({self._proveItStorageId(proof) for style_id, proof 
                        in KnownTruth.hyperlinked_proof_styles})
        
        # dereference old ones
        for old_ref in previous - current:
            self._removeReference(old_ref)
        
        # reference new one
        for new_ref in current - previous:
            self._addReference(new_ref)
        
        with open(reference_file, 'w') as f:
            for cur_ref in current:
                f.write(cur_ref + '\n')  
        
        if clear:
            os.remove(reference_file)
    
    def clearHyperlinkedObjectReferences(self):
        '''
        Remove all of the references to displayed expressions 
        and proofs of displayed known truths in this context.
        '''
        suffix = '_hyperlinked.pv_it'
        for filename in os.listdir(self.referenced_dir):
            if filename[-len(suffix):] == suffix:
                displayed_ref_path = os.path.join(self.referenced_dir, filename)
                with open(displayed_ref_path, 'r') as f:
                    for ref in f.readlines():
                        self._removeReference(ref.strip())
                os.remove(displayed_ref_path)            
    
    def clean(self):
        '''
        Clean the __pv_it directory by erasing anything with a reference
        count of zero.
        '''
        for sub_dir in os.listdir(self.pv_it_dir):
            if sub_dir == '_referenced_':
                continue
            sub_path = os.path.join(self.pv_it_dir, sub_dir)
            if os.path.isdir(sub_path):
                # assume this is a hash directory for a prove-it object if it isn't in '_referenced_'
                hash_directory = sub_dir 
                if self._getRefCount(hash_directory) == 0:
                    self._removeReference(hash_directory)

    def containsAnyExpression(self):
        '''
        Returns True if the __pv_it directory contains any expressions based
        on whether or not there are sub-directories of the __pv_it directory
        other than "_referenced_" after calling "clean()".
        '''
        self.clean()
        for sub_dir in os.listdir(self.pv_it_dir):
            if sub_dir == '_referenced_': # or sub_dir == 'failed_common_import.txt':
                continue
            return True # a sub-directory other than _referenced_; assume it is for an expression
        return False
        
                        
    """    
    # This is not good to do if there are external references
           
    def erase(self):
        '''
        Erase the entire __pv_it directory.
        '''
        self._proveItObjects.clear()
        pv_it_dir = os.path.join(self.directory, '__pv_it')
        if not os.path.isdir(pv_it_dir): return
        for hash_dir in os.listdir(pv_it_dir):
            hash_path = os.path.join(pv_it_dir, hash_dir)
            for pv_it_file in os.listdir(hash_path):
                os.remove(os.path.join(hash_path, pv_it_file))
            os.rmdir(hash_path)
        os.rmdir(pv_it_dir)
    """
    
class StoredSpecialStmt:
    def __init__(self, context, name, kind):
        '''
        Base class of StoredAxiom and StoredTheorem initialization.
        '''
        self.context = context
        self.name = name
        self.kind = kind
        if kind == 'axiom':
            self.path = os.path.join(self.context._storage.referenced_dir, 'axioms', self.name)
        elif kind == 'theorem':
            self.path = os.path.join(self.context._storage.referenced_dir, 'theorems', self.name) 
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")

    def __str__(self):
        return self.context.name + '.' + self.name
    
    def remove(self, keepPath=False):
        '''
        Remove the axiom or theorem and all references to it and any proofs
        that depend upon it.
        '''
        from .context import Context
        # remove the reference to the expression to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'expr.pv_it'), 'r') as f:
            expr_id = f.read()
            storage = self.context._storage
            storage._removeReference(expr_id)
            hash_path = storage._storagePath(expr_id)
            if not os.path.isdir(hash_path):
                # remove name.txt and kind.txt that mark the stored expression as a special statement
                special_name_file = os.path.join(hash_path, 'name.txt')
                if os.path.isfile(special_name_file):
                    os.remove(special_name_file)                    
                special_kind_file = os.path.join(hash_path, 'kind.txt')
                if os.path.isfile(special_kind_file):
                    os.remove(special_kind_file)      
                # remove the "special" expression notebook 
                expr_notebook = os.path.join(hash_path, 'expr.ipynb')
                if os.path.isfile(expr_notebook):
                    os.remove(expr_notebook)
                # resurrect the original expression notebook
                orig_expr_notebook = os.path.join(hash_path, 'orig_expr.ipynb')
                if os.path.isfile(orig_expr_notebook):
                    os.rename(orig_expr_notebook, expr_notebook)
        # remove invalidated proofs that use this axiom/theorem
        dependentTheorems = self.readDependentTheorems()
        for dependent in dependentTheorems:
            Context.getStoredTheorem(dependent).removeProof()
        if not keepPath:
            # remove the entire directory for the axiom/theorem
            shutil.rmtree(self.path)
        
    def readDependentTheorems(self):
        '''
        Return the collection of theorems (as strings) that use this theorem/axiom directly.
        '''
        theorems = []
        usedByFilename = os.path.join(self.path, 'usedBy.txt')
        if not os.path.isfile(usedByFilename):
            return theorems # return the empty list
        with open(usedByFilename, 'r') as usedByFile:
            for line in usedByFile:
                theorems.append(line.strip())
        return theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the given 
        theorem or axiom directly or indirectly.
        '''
        from .context import Context
        toProcess = set(self.readDependentTheorems())
        processed = set()
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            processed.add(nextTheorem)
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            dependents = set(storedTheorem.readDependentTheorems())
            # add anything new to be processed
            toProcess.update(dependents.difference(processed))
        return processed

    def _removeEntryFromFile(self, filename, entryToRemove):
        '''
        Removes a specific entry from a file.
        '''
        # obtain all lines that are NOT the specified link to be removed
        remaining = []
        with open(os.path.join(self.path, filename), 'r') as f:
            for line in f:
                line = line.strip()
                if line != entryToRemove:
                    remaining.append(line)
        # re-write usedBy.txt with all of the remaining lines
        with open(os.path.join(self.path, filename), 'w') as f:
            for line in remaining:
                f.write(line + '\n')
    
    def _countEntries(self, filename):
        '''
        Returns the number of entries in a particular file.
        '''
        count = 0
        with open(os.path.join(self.path, filename), 'r') as f:
            for line in f:
                count += 1
        return count

    def _removeUsedByEntry(self, usedByTheorem):
        '''
        Remove a particular usedByTheorem entry in the usedBy.txt for this
        stored axiom or theorem.
        '''
        self._removeEntryFromFile('usedBy.txt', str(usedByTheorem))
    
class StoredAxiom(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredAxioms object for managing an axioms's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'axiom')
    
    def getDefLink(self):
        '''
        Return the link to the axiom definition in the _axioms_ notebook.
        '''
        axioms_notebook_link = relurl(os.path.join(self.context.getPath(), '_axioms_.ipynb'))
        return axioms_notebook_link + '#' + self.name

class StoredTheorem(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredTheorem object for managing a theorem's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'theorem')

    def getProofLink(self):
        '''
        Return the link to the theorem's proof notebook.
        '''
        return relurl(os.path.join(self.context.getPath(), '_proofs_', self.name + '.ipynb'))

    def remove(self, keepPath=False):
        if self.hasProof():
            # must remove the proof first
            self.removeProof()
        StoredSpecialStmt.remove(self, keepPath)

    def readDependencies(self):
        '''
        Returns the used set of axioms and theorems (as a tuple of sets
        of strings) that are used by the given theorem as recorded in the database.
        '''
        usedAxiomNames = set()
        usedTheoremNames = set()
        for usedStmts, usedStmtsFilename in ((usedAxiomNames, 'usedAxioms.txt'), (usedTheoremNames, 'usedTheorems.txt')):
            try:
                with open(os.path.join(self.path, usedStmtsFilename), 'r') as usedStmtsFile:
                    for line in usedStmtsFile:
                        line = line.strip()
                        usedStmts.add(line)
            except IOError:
                pass # no contribution if the file doesn't exist
        return (usedAxiomNames, usedTheoremNames)

    def recordPresumedContexts(self, presumed_context_names):
        '''
        Record information about what other contexts are
        presumed in the proof of this theorem.
        '''
        from .context import Context
        for presumed_context in presumed_context_names:
            # raises an exception if the context is not known
            Context.getContext(presumed_context) 
        presuming_str = '\n'.join(presumed_context_names) + '\n'
        presuming_file = os.path.join(self.path, 'presumed_contexts.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                if presuming_str == f.read():
                    return # unchanged; don't need to record anything
        with open(presuming_file, 'w') as f:
            f.write(presuming_str)

    def presumedContexts(self):
        '''
        Return the list of presumed contexts.
        '''
        # first read in the presuming info
        presumptions = []
        presuming_file = os.path.join(self.path, 'presumed_contexts.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                for presumption in f.readlines():
                    presumption = presumption.strip()
                    if presumption == '': continue
                    presumptions.append(presumption)
        return presumptions
    
    def recordPresumedTheorems(self, explicitly_presumed_theorem_names):
        '''
        Record information about what other theorems are
        explicitly presumed in the proof of this theorem.
        '''
        presuming_str = '\n'.join(explicitly_presumed_theorem_names) + '\n'
        presuming_file = os.path.join(self.path, 'presumed_theorems.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                if presuming_str == f.read():
                    return # unchanged; don't need to record anything
        with open(presuming_file, 'w') as f:
            f.write(presuming_str)
        
        # The context's theorem dependency order is now stale
        # and needs to be updated:
        self.context._storage.invalidateTheoremDependencyOrder()
    
    def explicitlyPresumedTheoremNames(self):
        '''
        Return the list of names of explicitly presumed theorems
        (indicated after 'presuming' in the proof notebook). 
        '''
        presumptions = []
        presuming_file = os.path.join(self.path, 'presumed_theorems.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                for presumption in f.readlines():
                    presumption = presumption.strip()
                    if presumption == '': continue
                    presumptions.append(presumption)
        return presumptions        
    
    """
    def getRecursivelyPresumedTheorems(self, presumed_theorems, presumption_chain=None):
        '''
        Append presumed theorem objects to 'presumed_theorems'.
        For each theorem, do this recursively.
        presumption_chain is used internally to detect and reveal
        circular dependencies.
        '''
        from .context import Context
        from .proof import CircularLogicLoop
        # first get the directly presumed theorems
        presumptions = self.directlyPresumedTheorems()
        if presumption_chain is None:
            presumption_chain = [str(self)]
        else:
            presumption_chain.append(str(self))
        # Iterate through each presuming string and add it as
        # a context name or a theorem.  For theorem's, recursively
        # add the presuming information.
        for presumption in presumptions:
            if not isinstance(presumption, str):
                raise ValueError("'presumptions' should be a collection of strings for context names and/or full theorem names")
            context_name, theorem_name = presumption.rsplit('.', 1)
            thm = Context.getContext(context_name).getTheorem(theorem_name)
            if str(thm) in presumption_chain:
                index = presumption_chain.index(str(thm))
                raise CircularLogicLoop(presumption_chain[index:]+[str(thm)], thm)
            # add the theorem and anything presumed by that theorem to the set of presumed theorems/contexts
            if thm not in presumed_theorems:
                presumed_theorems.add(thm)
                thm._storedTheorem().getRecursivelyPresumedTheorems(presumed_theorems, list(presumption_chain))
    """
    def getAllPresumedTheoremNames(self):
        '''
        Return the set of full names of theorems that are presumed directly or indirectly
        by this one.
        '''
        return self.context._storage.getAllPresumedTheoremNames(self.name)
    
    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  Updates
        dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
        and proven dependency indicators (various provenTheorems.txt files 
        for theorems that depend upon this one) appropriately.
        '''
        from proveit._core_ import Proof
        from .context import Context
              
        # add a reference to the new proof
        proofId = self.context._storage._proveItStorageId(proof)
        self.context._storage._addReference(proofId)
        
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()
                    
        # record the proof id
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
        
        usedAxiomNames = [str(usedAxiom) for usedAxiom in proof.usedAxioms()]
        usedTheoremNames = [str(usedTheorem) for usedTheorem in proof.usedTheorems()]
        
        # Remove usedBy links that are obsolete because the proof has changed
        prevUsedAxiomNames, prevUsedTheoremNames = self.readDependencies()
        for prevUsedAxiom in prevUsedAxiomNames:
            if prevUsedAxiom not in usedAxiomNames:
                Context.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(str(self))
        for prevUsedTheorem in prevUsedTheoremNames:
            if prevUsedTheorem not in usedTheoremNames:
                Context.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(str(self))

        storedUsedAxiomNames = [Context.getStoredAxiom(usedAxiomName) for usedAxiomName in usedAxiomNames]
        storedUsedTheoremNames = [Context.getStoredTheorem(usedTheoremName) for usedTheoremName in usedTheoremNames]
        
        # record axioms/theorems that this theorem directly uses
        for storedUsedStmts, usedStmtsFilename in ((storedUsedAxiomNames, 'usedAxioms.txt'), (storedUsedTheoremNames, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for storedUsedStmt in sorted(storedUsedStmts, key=lambda stmt:str(stmt)):
                    self.context._storage._includeMutualReferences(storedUsedStmt.context)
                    usedStmtsFile.write(str(storedUsedStmt) + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheoremNames:
                if Context.getStoredTheorem(usedTheorem).isComplete():
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the newly proven theorem
        for storedUsedStmts, prevUsedStmts in ((storedUsedAxiomNames, prevUsedAxiomNames), (storedUsedTheoremNames, prevUsedTheoremNames)):
            for storedUsedStmt in storedUsedStmts:
                if str(storedUsedStmt) not in prevUsedStmts: # otherwise the link should already exist
                    with open(os.path.join(storedUsedStmt.path, 'usedBy.txt'), 'a') as usedByFile:
                        usedByFile.write(str(self) + '\n')
        
        # if this proof is complete (all of the theorems that it uses are complete) then
        # propagate this information to the theorems that depend upon this one.
        self._propagateCompletion()
    
    def hasProof(self):
        '''
        Returns True iff a proof was recorded for this theorem.
        '''
        return os.path.isfile(os.path.join(self.path, 'proof.pv_it'))
    
    def numUsedTheorems(self):
        try:
            return self._countEntries('usedTheorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason

    def numCompleteUsedTheorems(self):
        try:
            return self._countEntries('completeUsedTheorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason
    
    def isComplete(self):
        '''
        Return True iff this theorem has a proof and all theorems that
        that it uses are also complete.
        '''
        if not self.hasProof():
            return False # Cannot be complete if there is no proof for this theorem
        # If all used theorems have are complete (and this theorem has a proof),
        # then this theorem is complete.
        return self.numUsedTheorems() == self.numCompleteUsedTheorems()
    
    def _propagateCompletion(self):
        '''
        If this theorem is complete, then let its dependents know.  If this
        update causes a dependent to become complete, propagate the news onward.
        '''
        from .context import Context
        if self.isComplete():
            # This theorem has been completely proven.  Let the dependents know.
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                storedDependent = Context.getStoredTheorem(dependent)
                with open(os.path.join(storedDependent.path, 'completeUsedTheorems.txt'), 'a') as f:
                    f.write(str(self) + '\n')
                # propagate this recursively in case self's theorem was the final
                # theorem to complete the dependent
                storedDependent._propagateCompletion()
                        
    def removeProof(self):
        '''
        Erase the proof of this theorem from the database and all obsolete
        links/references.
        '''     
        from .context import Context 
        wasComplete = self.isComplete() # was it complete before the proof was removed?
        # remove the reference to the proof to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'proof.pv_it'), 'r') as f:
            proof_id = f.read()
            self.context._storage._removeReference(proof_id)
        # Remove obsolete usedBy links that refer to this theorem by its old proof
        prevUsedAxiomNames, prevUsedTheoremNames = self.readDependencies()
        for usedAxiom in prevUsedAxiomNames:
            Context.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheoremNames:
            Context.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform dependents that
        # it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
        # remove 'proof.pv_it', 'usedAxioms.txt', 'usedTheorems.txt', and 'completeUsedTheorems.txt' for the theorem
        def removeIfExists(path):
            if os.path.isfile(path): os.remove(path)
        removeIfExists(os.path.join(self.path, 'proof.pv_it'))
        removeIfExists(os.path.join(self.path, 'usedAxioms.txt'))
        removeIfExists(os.path.join(self.path, 'usedTheorems.txt'))
        removeIfExists(os.path.join(self.path, 'completeUsedTheorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        usedAxiomNames, usedTheoremNames = self.readDependencies()
        requiredAxioms = usedAxiomNames # just a start
        requiredTheorems = set()
        processed = set()
        toProcess = usedTheoremNames
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                requiredTheorems.add(nextTheorem)
                processed.add(nextTheorem)
                continue
            usedAxiomNames, usedTheoremNames = storedTheorem.readDependencies()
            requiredAxioms.update(usedAxiomNames)
            for usedTheorem in usedTheoremNames:
                if usedTheorem not in processed:
                    toProcess.add(usedTheorem)
            processed.add(nextTheorem)
        return (requiredAxioms, requiredTheorems)
    
    def allUsedTheoremNames(self):
        '''
        Returns the set of names of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        _, usedTheoremNames = self.readDependencies()
        allUsedTheoremNames = set()
        processed = set()
        toProcess = usedTheoremNames
        while len(toProcess) > 0:
            nextTheoremName = toProcess.pop()
            allUsedTheoremNames.add(nextTheoremName)
            storedTheorem = Context.getStoredTheorem(nextTheoremName)
            if not storedTheorem.hasProof():
                processed.add(nextTheoremName)
                continue
            _, usedTheoremNames = storedTheorem.readDependencies()
            for usedTheoremName in usedTheoremNames:
                if usedTheoremName not in processed:
                    toProcess.add(usedTheoremName)
            processed.add(nextTheoremName)
        return allUsedTheoremNames 

    def _undoDependentCompletion(self, usedTheoremName):
        '''
        Due to the proof being removed, a dependent theorem is no longer complete.
        This new status must be updated and propagated.
        '''
        from .context import Context
        wasComplete = self.isComplete() # was it complete before?
        # remove the entry from completeUsedTheorems.txt
        self._removeEntryFromFile('completeUsedTheorems.txt', usedTheoremName)
        if self.isComplete():
            raise Exception('Corrupt _certified_ database')
        # If this theorem was previously complete before, we need to inform 
        # dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))


