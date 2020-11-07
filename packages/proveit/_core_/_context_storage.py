import hashlib, os
import shutil
import sys
import importlib
import itertools
import json
from io import StringIO
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
    the _sub_contexts_.txt file which is in the main directory because
    it should be committed to the repository (unlike the __pv_it
    directory which can all be re-generated).
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
        if not os.path.isdir(self.pv_it_dir):
            # make the __pv_it directory
            os.makedirs(self.pv_it_dir)
        
        if self.isRoot():
            # If this is a root context, let's add the directory above 
            # the root to sys.path if it is needed.
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
            # map context names to paths for other known root contexts
            # in paths.txt
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

        # Map (kind, name) pair to the corresponding expression
        # hash for special expressions (axioms, theorems, 
        # and common expressions).
        self._kindname_to_exprhash = dict()
        
        # Map the special object kind ('common', 'axiom', or 
        # 'theorem') to a dictionary mapping names to storage 
        # identifiers:
        self._special_hash_ids = {'common':None, 'axiom':None,
                                  'theorem':None}
        
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
        
        # Map folder names to corresponding ContextFolderStorage
        # objects.
        self._folder_storage_dict = dict()
        
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
    
    def contextFolderStorage(self, folder):
        '''
        Return the ContextFolderStorage object associated with the
        context of this ContextStorage and the folder.
        '''
        if folder not in self._folder_storage_dict:
            self._folder_storage_dict[folder] = \
                ContextFolderStorage(self, folder)
        return self._folder_storage_dict[folder]
    
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

    def _includeReference(self, referencedContext):
        '''
        Include a path reference from a root Context to another root 
        Context via the paths.txt file so the name of the context
        will be associated with the corresponding directory.
        '''
        root = self.rootContextStorage
        referenced_root = referencedContext._storage.rootContextStorage
        if root is not referenced_root:
            referenced_root_name = referenced_root.name
            if referenced_root_name not in self.referencedContextRoots:
                with open(self.pathsFilename, 'a') as pathsFile:
                    pathsFile.write(referenced_root_name + ' ' 
                                    + referenced_root.directory + '\n')
                self.referencedContextRoots.add(referenced_root_name)
    
    def _loadTheoremDependencyOrder(self):
        '''
        Load the theorem dependency order that is stored in 
        'theorem_dependency_order.txt'.
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
                    assert theorem_name not in theorems_set, \
                        ("Should not have duplicated theorem names: %s"
                         %theorem_name)
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
            
    @staticmethod
    def _kind_to_folder(kind):
        if kind in ('axiom', 'theorem'):
            return kind + 's'
        elif kind == 'common':
            return kind
        else:
            raise ValueError("Unexpected kind: %s"%kind)        
    
    @staticmethod
    def _folder_to_kind(folder):
        if folder in ('axioms', 'theorems'):
            return folder[:-1]
        elif folder == 'common':
            return folder
        else:
            raise ValueError("Expecting 'axioms', 'theorems' or 'common', "
                             "not %s."%folder)   

    def setCommonExpressions(self, names, definitions):
        '''
        Set the common expressions of the context.
        '''
        return self.setSpecialExpressions(names, definitions, 'common')

    def setSpecialExpressions(self, names, definitions, kind):
        '''
        Set the common expressions, axioms, or theorems of the context.
        '''
        from proveit._core_.proof import Axiom, Theorem
        if kind=='common':
            self._common_expr_names = None # force a reload            
        elif kind=='axiom':
            self._axiom_names = None # force a reload
            # Convert definitions from expressions to KnownTruth objects
            # corresponding to the Axioms:
            definitions = {name:Axiom(expr, self.context, name).provenTruth 
                           for name, expr in definitions.items()}
        elif kind == 'theorem':
            self._theorem_names = None # force a reload
            # Convert definitions from expressions to KnownTruth objects
            # corresponding to the Theorems:
            definitions = {name:Theorem(expr, self.context, name).provenTruth 
                           for name, expr in definitions.items()}
        self._setSpecialObjects(names, definitions, kind)
    
    def _setSpecialObjects(self, names, definitions, kind):
        folder = ContextStorage._kind_to_folder(kind)
        names_file = os.path.join(self.pv_it_dir, folder, 'name_to_hash.txt')
        context_name = self.name
        special_hash_ids = self._special_hash_ids[kind] = dict()
        
        # get any previous common expression ids to see if their 
        # reference count needs to be decremented.
        hash_to_old_name = dict() 
        old_name_to_hash = dict()
        if os.path.isfile(names_file):
            with open(names_file, 'r') as f:
                for line in f.readlines():
                    name, hash_id = line.split()
                    hash_to_old_name[hash_id] = name
                    old_name_to_hash[name] = hash_id
        
        # write new common expression ids
        new_hash_ids = set()
        with open(names_file, 'w') as f:
            for name in names:
                obj = definitions[name]
                if kind=='common':
                    expr = obj
                else:
                    expr = obj.expr
                # record the special expression in this context object
                context_folder_storage = \
                    self.context._contextFolderStorage(folder)
                # get the expression id to be stored on 'commons.pv_it'           
                hash_id = context_folder_storage._proveItStorageId(obj)
                if kind=='common':
                    expr_id = hash_id
                else:
                    expr_id = context_folder_storage._proveItStorageId(expr)
                if hash_id in hash_to_old_name:
                    if hash_to_old_name[hash_id] != name:
                        print("Renaming %s to %s"%(hash_to_old_name[hash_id],
                                                   name))
                    # same expression as before
                    hash_to_old_name.pop(hash_id)
                else:
                    # new expression not previously in the common expressions liest:
                    new_hash_ids.add(hash_id) 
                # Store the name and the expression id.
                f.write(name + ' ' + hash_id + '\n')
                special_hash_ids[name] = hash_id
                self._kindname_to_exprhash[(kind, name)] = expr_id
                context_folder_storage._exprhash_to_name[expr_id] = name
                if folder != 'common':
                    kind = folder[:-1]
                    if name not in old_name_to_hash:
                        # added special statement
                        print('Adding %s %s to %s context'%
                              (kind, name, context_name))
                    elif old_name_to_hash[name] != hash_id:
                        # modified special statement. remove the old one first.
                        print('Modifying %s %s in %s context'%
                              (kind, name, context_name))
                        StoredSpecialStmt.remove_dependency_proofs(
                                self.context, kind, old_name_to_hash[name])
                    # record the axiom/theorem id (creating the directory
                    # if necessary)
                    special_statement_dir = os.path.join(
                            context_folder_storage.path, name)
                    if not os.path.isdir(special_statement_dir):
                        os.mkdir(special_statement_dir)
                    with open(os.path.join(special_statement_dir, 
                                           'used_by.txt'), 'w') as _:
                        # used_by.txt must be created but 
                        pass # initially empty
        # Indicate special expression removals.
        for hash_id, name in hash_to_old_name.items():
            if folder == 'common':
                print("Removing %s from %s context"%
                      (name, context_name))
            else:
                print("Removing %s %s from %s context"%
                      (kind, name, context_name))
                StoredSpecialStmt.remove_dependency_proofs(
                        self.context, kind, hash_id)
        
        if kind=='theorem':
            # update the theorem dependency order when setting the
            # theorems
            self._updateTheoremDependencyOrder(names)            

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
    
    def loadSpecialNames(self):
        '''
        Load all of the common expresisons, axioms, and theorems,
        stored for this context.
        '''
        for kind in ('common', 'axiom', 'theorem'):
            special_hash_ids = self._special_hash_ids[kind]
            if special_hash_ids is None:
                # while the names are read in, the expr id map will 
                # be generated
                list(self._loadSpecialNames(kind))
    
    def _loadCommonExpressionNames(self):
        return self._loadSpecialExpressionNames('common')
    
    def _loadSpecialStatementNames(self, kind):
        return self._loadSpecialNames(kind)
        
    def _loadSpecialNames(self, kind):
        '''
        Yield names of axioms/theorems or common expressions
        '''
        folder = ContextStorage._kind_to_folder(kind)
        context_folder_storage = self.contextFolderStorage(folder)
        name_to_hash_filename = os.path.join(self.pv_it_dir, folder, 
                                             'name_to_hash.txt')
        if os.path.isfile(name_to_hash_filename):
            special_hash_ids = self._special_hash_ids[kind] = dict()
            with open(name_to_hash_filename, 'r') as f:
                for line in f.readlines():
                    name, hash_id = line.split()
                    special_hash_ids[name] = hash_id

                    if kind == 'common':
                        expr_id = hash_id
                    else:
                        # For an axiom or theorem, we must read in the
                        # unique_rep.pv_it file to get the expr_id.
                        unique_rep_filename = os.path.join(
                                self.pv_it_dir, folder, hash_id, 
                                'unique_rep.pv_it')
                        with open(unique_rep_filename, 'r') as f:
                            rep = f.read()
                        # hash ids will be relative to the corresponding
                        # folder, appropriately so.
                        exprids = \
                            context_folder_storage.\
                            _extractReferencedStorageIds(
                                    rep, context_folder_storage.context.name, 
                                    context_folder_storage.folder)
                        expr_id = exprids[0]
                    self._kindname_to_exprhash[(kind, name)] = expr_id
                    context_folder_storage._exprhash_to_name[expr_id] = name
                    yield name
    
    def getAxiomHash(self, name):
        '''
        Return the hash folder where information about the axiom of the 
        given name is stored (stored on the 'axioms' context storage
        folder).
        '''
        list(self._loadSpecialNames('axiom'))
        return self._special_hash_ids['axiom'][name]

    def getTheoremHash(self, name):
        '''
        Return the path where information about the theorem of the given 
        name is stored (stored on the 'theorems' context storage
        folder).
        '''
        list(self._loadSpecialNames('theorem'))
        return self._special_hash_ids['theorem'][name]
            
    def getCommonExpr(self, name):
        '''
        Return the Expression of the common expression in this context
        with the given name.
        '''
        expr = self._getSpecialExpression('common', name)
        self._loadedCommonExprs[name] = expr
        return expr
    
    def getAxiom(self, name):
        '''
        Return the Axiom of the given name in this context.
        '''
        from proveit._core_.proof import Axiom
        if name in self._loadedAxioms:
            return self._loadedAxioms[name]
        expr = self._getSpecialExpression('axiom', name)
        axiom = self._loadedAxioms[name] = Axiom(expr, self.context, name)
        return axiom

    def getTheorem(self, name):
        '''
        Return the Theorem of the given name in this context.
        '''
        from proveit._core_.proof import Theorem
        if name in self._loadedTheorems:
            return self._loadedTheorems[name]
        expr = self._getSpecialExpression('theorem', name)
        thm = self._loadedTheorems[name] = Theorem(expr, self.context, name)
        return thm
        
    def _getSpecialExpression(self, kind, name):
        from .context import Context, UnsetCommonExpressions
        folder = ContextStorage._kind_to_folder(kind)
        special_hash_ids = self._special_hash_ids[kind]
        if special_hash_ids is None:
            # while the names are read in, the hash id map will 
            # be generated
            list(self._loadSpecialNames(kind))
            special_hash_ids = self._special_hash_ids[kind]
        if special_hash_ids is None:
            if kind=='common':
                raise UnsetCommonExpressions(self.name)
            raise KeyError("%s of name '%s' not found"%(kind, name))  
            
        # set the default Context in case there is a Literal
        prev_context_default = Context.default
        Context.default = self.context 
        context_folder_storage = self.contextFolderStorage(folder)
        
        # make and return expression
        expr_id = self._kindname_to_exprhash[(kind, name)]
        try:
            expr = context_folder_storage.makeExpression(expr_id)
        finally:
            Context.default = prev_context_default # reset the default Context 
        return expr
    
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
                raise KeyError("Theorem %s not found in context %s"%(theorem_name, context.name))
            if presumption_name in presumption_chain:
                chain_index = presumption_chain.index(presumption_name)
                presumption = context.getTheorem(theorem_name)
                raise CircularLogicLoop(presumption_chain[chain_index:]+[presumption_name], presumption)
            if presumption_name not in presumed_theorem_names:
                presumed_theorem_names.add(presumption_name)
                context._storage._allPresumedTheoremNames(theorem_name, presumed_theorem_names, presumption_chain+[presumption_name])

    def thmProofNotebook(self, theorem_name, expr):
        '''
        Return the relative url to the proof notebook, 
        creating it if it does not already exist.
        '''
        proofs_path = os.path.join(self.directory, '_proofs_')
        filename = os.path.join(proofs_path, '%s.ipynb'%theorem_name)
        if os.path.isfile(filename):
            # Check the theorem name and make sure the capitalization
            # is the same.  If not, revise it appropriately.
            existing_theorem_name = self._proofNotebookTheoremName(filename)
            if existing_theorem_name is None:
                # The format is not correct; stash this one and 
                # generate a new one.
                self._stashNotebook(filename)
            else:
                if existing_theorem_name != theorem_name:
                    # update with the new capitalization
                    with open(filename, 'r') as proof_notebook:
                        nb = proof_notebook.read()
                    nb = nb.replace(existing_theorem_name, theorem_name)
                    # remove the file before creating again to force the
                    # new capitolization (e.g., in Windows where
                    # capitolization can be flexible)
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
        Given a theorem name and hash directory, generate the generic
        startof a proof notebook using the template.
        '''
        import proveit
        proveit_path = os.path.split(proveit.__file__)[0]
        # read the template and change the contexts as appropriate
        with open(os.path.join(proveit_path, '..', 
                               '_theorem_proof_template_.ipynb'), 
                'r') as template:
            nb = template.read()
            nb = nb.replace('#THEOREM_NAME#', theorem_name)
            context_links = self.context.links(
                    os.path.join(self.directory, '_proofs_'))
            nb = nb.replace('#CONTEXT#', context_links)
        return nb
    
    def _proofNotebookTheoremName(self, filename):
        '''
        Return the theorem name extracted from the proof notebook.
        '''
        with open(filename, 'r') as proof_notebook:
            nb = proof_notebook.read()
            # the theorem name should come after "_theorems_.ipynb#" 
            # in the notebook
            match =  re.search(r'_theorems_\.ipynb\#([_a-zA-Z]\w*)', nb)
            if match is None: return None
            return match.groups()[0]
            
    def stashExtraneousThmProofNotebooks(self, theorem_names):
        '''
        For any proof notebooks for theorem names not included in the 
        given theorem_names, stash them or remove them if they are 
        generic notebooks.
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
            
            # may be set to True below if it is a generic notebook
            remove_file = False 
            
            # next, let's see if this is a generic notebook by 
            # extracting its info, building the generic version, and
            # comparing.
            theorem_name = self._proofNotebookTheoremName(filename)
            if theorem_name is not None:
                generic_version = self._generateGenericThmProofNotebook(
                        theorem_name)        
                with open(filename, 'r') as notebook:
                    if generic_version == notebook.read():
                        # just remove it, it is generic
                        remove_file = True
            
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
        print("Stashing %s to %s in case it is needed."%
              (relurl(filename), relurl(new_filename)))
        os.rename(filename, new_filename)

class ContextFolderStorage:
    # The active context folder storage (e.g., corresponding to the
    # notebook being executed).
    active_context_folder_storage = None
    
    # Map style ids of Prove-It object (Expressions, KnownTruths, and 
    # Proofs) to a (ContextFolderStorage, hash_id) tuple where it is
    # being stored.
    proveit_object_to_storage = dict()
    
    def __init__(self, context_storage, folder):
        self.context_storage = context_storage
        self.context = context_storage.context
        self.pv_it_dir = self.context_storage.pv_it_dir
        self.folder = folder
        self.path = os.path.join(self.pv_it_dir, folder)
        if not os.path.isdir(self.path):
            # make the folder
            os.makedirs(self.path)
        
        # For 'common', 'axioms', 'theorems' folders, we map
        # expression hash folder names to the name of the
        # axiom, theorem, or common expression.
        self._exprhash_to_name = dict()
    
    @staticmethod
    def getFolderStorageOfExpr(expr):
        '''
        Obtain the ContextFolderStorage that 'owns' the given
        expression, or the default ContextFolderStorage.
        '''
        proveit_obj_to_storage = ContextFolderStorage.proveit_object_to_storage
        if expr._style_id in proveit_obj_to_storage:
            (context_folder_storage, _) =\
                proveit_obj_to_storage[expr._style_id]
            return context_folder_storage
        else:
            # Return the "active context folder storage" as default.
            # This is set by the %begin Prove-It magic command.
            return ContextFolderStorage.active_context_folder_storage
    
    def specialExprAddress(self, expr_hash_id):
        '''
        A special expression "address" consists of a kind ('common', 
        'axiom', or 'theorem'), module and the name of the expression.
        Provided that the given expression is one of the special 
        expressions of this context, return the address as a tuple.
        '''
        kind = ContextStorage._folder_to_kind(self.folder)
        name = self._exprhash_to_name[expr_hash_id]
        if kind == 'axiom' or kind=='theorem':
            name = name + '.expr'
        return kind, self.context_storage._specialExprModules[kind], name
        
    @staticmethod
    def retrieve_png(expr, latex, configLatexToolFn):
        '''
        Find the expr.png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and relative url where the png is stored as 
        a tuple.
        '''
        context_folder_storage = \
            ContextFolderStorage.getFolderStorageOfExpr(expr)
        return context_folder_storage._retrieve_png(
                expr, latex, configLatexToolFn)
    
    def _retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Helper method of retrieve_png.
        '''
        (context_folder_storage, hash_directory) = self._retrieve(expr)
        assert context_folder_storage==self, \
            "How did the context end up different from expected??"
        # generate the latex and png file paths, from pv_it_filename and
        # the distinction 
        latex_path = os.path.join(self.path, hash_directory, 'expr.latex')
        png_path = os.path.join(self.path, hash_directory, 'expr.png')
        # check if the latex file exists, is consistent with the given 
        # latex string, and if the png file exists.
        if os.path.isfile(latex_path):
            # latex file exists.  read it ans see if it the same as the
            # given latex string
            with open(latex_path) as latex_file:
                if latex_file.read() == latex:
                    # the latex files are the same, try to read the png
                    # file
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
        # the 'matplotlib' backend can do some BAD rendering in my 
        # experience (like \lnot rendering as lnot in some contexts)
        png = latex_to_png(latex, backend='dvipng', wrap=True) 
        if png is None:
            raise Exception(
                    "Unable to use 'dvipng' backend to compile LaTeX.\n"
                    "Be sure a LaTeX distribution is installed.")
        return png
       
    def _proveItStorageId(self, proveItObjectOrId):
        '''
        Retrieve a unique id for the Prove-It object based upon its 
        pv_it filename from calling _retrieve.
        '''
        if isinstance(proveItObjectOrId, str):
            return proveItObjectOrId
        else:
            if isinstance(proveItObjectOrId, int):
                # assumed to be a style id if it's an int
                style_id = proveItObjectOrId 
                (context_folder_storage, hash_directory) = \
                    ContextFolderStorage.proveit_object_to_storage[style_id]
            else:
                (context_folder_storage, hash_directory) = \
                    self._retrieve(proveItObjectOrId)
            if context_folder_storage.context != self.context:
                context = context_folder_storage.context
                folder = context_folder_storage.folder
                self.context_storage._includeReference(context)
                return context.name + '.' + folder + '.' + hash_directory
            elif context_folder_storage.folder != self.folder:
                return context_folder_storage.folder + '.' + hash_directory                
            else:
                return hash_directory
    
    def _split(self, proveItStorageId):
        '''
        Split the given storage-id into a context name, folder, and 
        the hash directory.  The context may be implicit (if in the
        same context it is referenced), in which case the context name 
        will be empty.
        '''
        if '.' in proveItStorageId:
            # in a different context or folder
            splitId = proveItStorageId.split('.')
            if len(splitId) == 2:
                folder, hash_directory = splitId[0], splitId[1]
                return '', folder, hash_directory
            else:
                context_name, folder, hash_directory = (
                        '.'.join(splitId[:-2]), splitId[-2], splitId[-1])
                return context_name, folder, hash_directory
        return '', self.folder, proveItStorageId
            
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with
        the given storage id.
        '''
        from .context import Context
        context_name, folder, hash_directory = self._split(proveItStorageId)
        if context_name == '':
            return os.path.join(self.pv_it_dir, folder, hash_directory)
        else:
            pv_it_dir = Context.getContext(context_name)._storage.pv_it_dir
            return os.path.join(pv_it_dir, folder, hash_directory)
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It
        object that is dependent upon the style.
        '''
        from proveit import Expression, KnownTruth, Proof
        prefix = None
        if isinstance(proveItObject, Expression):
            prefix = '' # No prefix for Expressions
        elif isinstance(proveItObject, KnownTruth):
             # prefix to indicate that it is a KnownTruth
            prefix = 'KnownTruth:'
        elif isinstance(proveItObject, Proof):
            prefix = 'Proof:' # prefix to indicate that it is a Proof
        else:
            raise NotImplementedError(
                    'Strorage only implemented for Expressions,'
                    'Statements (effectively), and Proofs')
        # Generate a unique representation using Prove-It object ids for
        # this storage to represent other referenced Prove-It objects.
        return prefix + proveItObject._generate_unique_rep(
                self._proveItStorageId)
    
    def _extractReferencedStorageIds(self, unique_rep, context_name, 
                                     folder, storage_ids=None):
        '''
        Given a unique representation string, returns the list of 
        Prove-It storage ids of objects that are referenced.  A 
        context_name may be given; if the Context is the one associated 
        with this Storage object then the default may be used.
        '''
        from proveit import Expression, KnownTruth, Proof
        if storage_ids is None:
            if unique_rep[:6] == 'Proof:':
                storage_ids = Proof._extractReferencedObjIds(unique_rep[6:])
            elif unique_rep[:11] == 'KnownTruth:':
                storage_ids = KnownTruth._extractReferencedObjIds(
                        unique_rep[11:])
            else:
                # Assumed to be an expression then
                storage_ids = Expression._extractReferencedObjIds(unique_rep)
        def relative_to_explicit_prefix(storage_id, context_name, folder):
            # If the exprId is relative to the context it is in, make the 
            # context explicit.
            split_id = storage_id.split('.')
            if len(split_id) == 2:
                return context_name + '.' + storage_id # explicit folder
            elif len(split_id) == 1:
                # convert local to explicit
                return context_name + '.' + folder + '.' + storage_id
            else:
                return storage_id # already explicit
        if context_name != '' or folder != self.folder:
            return [relative_to_explicit_prefix(storage_id, context_name,
                                                folder) 
                    for storage_id in storage_ids]
        return storage_ids
    
    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, KnownTruth, or 
        Proof.  Create it if it did not previously exist.  Return the 
        (context_folder_storage, hash_directory) pair where the 
        hash_directory is the directory name (within the context's
        __pv_it directory) based upon a hash of the unique 
        representation.
        '''
        from proveit import Literal, Proof
        from proveit._core_.proof import Axiom, Theorem
        proveit_obj_to_storage = ContextFolderStorage.proveit_object_to_storage
        if proveItObject._style_id in proveit_obj_to_storage:
            return proveit_obj_to_storage[proveItObject._style_id]
        if isinstance(proveItObject, Axiom):
            context_folder_storage = \
                proveItObject.context._contextFolderStorage('axioms')
        elif isinstance(proveItObject, Theorem):
            context_folder_storage = \
                proveItObject.context._contextFolderStorage('theorems')
        elif isinstance(proveItObject, Literal):
            # Literal's must be stored in the 'common' folder
            # of its context.
            context_folder_storage = \
                proveItObject.context._contextFolderStorage('common')            
        else:
            context_folder_storage = self
        if context_folder_storage is not self:
            # Stored in a different folder.
            return context_folder_storage._retrieve(proveItObject)
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of 
        # this hash value
        rep_hash = hashlib.sha1(unique_rep.encode('utf-8')).hexdigest()
        hash_path = os.path.join(self.path, rep_hash)
        # append the hash value with an index, avoiding collisions 
        # (that should be astronomically rare, but let's not risk it).
        index = 0
        while os.path.exists(hash_path + str(index)):
            indexed_hash_path = hash_path + str(index)
            unique_rep_filename = os.path.join(indexed_hash_path, 
                                               'unique_rep.pv_it')
            if not os.path.isfile(unique_rep_filename):
                # folder does not contain a unique_rep.pv_it file;
                # it may not have been completely erased before, but
                # let's just use it.
                break
            with open(unique_rep_filename, 'r') as f:
                rep = f.read()
                if rep != unique_rep:
                    # there is a hashing collision (this should be 
                    # astronomically rare, but we'll make sure just
                    # in case)
                    index += 1 # increment the index and try again
                    continue
            # found a match; it is already in storage
            # remember this for next time
            result = (self, rep_hash + str(index))
            proveit_obj_to_storage[proveItObject._style_id] = result
            return result
        indexed_hash_path = hash_path + str(index)
        # store the unique representation in the appropriate file
        if not os.path.exists(indexed_hash_path):
            os.mkdir(indexed_hash_path)
        with open(os.path.join(indexed_hash_path, 'unique_rep.pv_it'), 
                  'w') as f:
            f.write(unique_rep) 
        # remember this for next time
        result = (self, rep_hash + str(index))
        proveit_obj_to_storage[proveItObject._style_id] = result
        return result
    
    @staticmethod
    def expressionNotebook(expr, unofficialNameKindContext=None,
                           useActiveFolder=False):
        '''
        Return the path of the expression notebook, creating it if it
        does not already exist.  If 'unofficialNameKindContext' is
        provided, it should be the (name, kind, context) for a special 
        expression that is not-yet-official 
        (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        from proveit import Expression
        
        if not isinstance(expr, Expression):
            raise ValueError("'expr' should be an Expression object")
        
        if useActiveFolder:
            context_folder_storage = \
                ContextFolderStorage.active_context_folder_storage
        else:
            if unofficialNameKindContext is not None:
                name, kind, context = unofficialNameKindContext
                context_folder_storage = context._contextFolderStorage(
                        ContextStorage._kind_to_folder(kind))
            else:
                context_folder_storage = \
                    ContextFolderStorage.getFolderStorageOfExpr(expr)
        
        return context_folder_storage._expressionNotebook(
                expr, unofficialNameKindContext)

    def _expressionNotebook(self, expr, unofficialNameKindContext=None):
        '''
        Helper method of expressionNotebook.
        '''
        import proveit
        proveit_path = os.path.split(proveit.__file__)[0]
        sys.path.append(os.path.join(proveit_path, '..', '..'))
        from nbstripout.nbstripout import clean_nb
        from proveit import expressionDepth
        from proveit._core_.proof import Axiom, Theorem
        from .context import Context
        
        # Determine the kind and name (if it is a "special" expression),
        # and appropriate template to be used.
        if unofficialNameKindContext is not None:
            template_name = '_unofficial_special_expr_template_.ipynb'
            name, kind, context = unofficialNameKindContext
        else:
            # Is this a "special" expression?
            try:
                expr_id = self._proveItStorageId(expr)
                name = self._exprhash_to_name[expr_id]
                kind = ContextStorage._folder_to_kind(self.folder)
            except KeyError:
                kind = None
            if kind is not None:
                if kind=='common':
                    template_name = '_common_expr_template_.ipynb'
                else:
                    template_name = '_special_expr_template_.ipynb'
            else:
                template_name = '_expr_template_.ipynb'    
        
        # Determine the appropriate hash folder to store the
        # expression notebook in.
        obj = expr
        if kind=='axiom':
            # Store this "special" notebook if the hash for the
            # KnownTruth object associated with the Axiom.
            obj = Axiom(expr, self.context, name).provenTruth
        elif kind=='theorem':
            # Store this "special" notebook if the hash for the
            # KnownTruth object associated with the Theorem.
            obj = Theorem(expr, self.context, name).provenTruth
        context_folder_storage, hash_directory = self._retrieve(obj)
        assert context_folder_storage == self
        full_hash_dir = os.path.join(self.path, hash_directory)
        
        expr_classes_and_constructors = set()
        unnamed_subexpr_occurences = dict()
        named_subexpr_addresses = dict()
        # maps each class name or special expression name to a list of 
        # objects being represented; that way we will know whether we 
        # can use the abbreviated name or full address.
        named_items = dict() 
        self._exprBuildingPrerequisites(
                expr, expr_classes_and_constructors, 
                unnamed_subexpr_occurences, named_subexpr_addresses, 
                named_items, 
                can_self_import = (unofficialNameKindContext is None),
                isSubExpr=False)
        # find sub-expression style ids that are used multiple times, 
        # these ones will be assigned to a variable
        multiuse_subexprs = [sub_expr for sub_expr, count 
                             in unnamed_subexpr_occurences.items() 
                             if count > 1]
        # sort the multi-use sub-expressions so that the shallower ones
        # come first
        _key = lambda expr_and_styleid : expressionDepth(expr_and_styleid[0])
        multiuse_subexprs = sorted(multiuse_subexprs, key = _key)
        
        # map modules to lists of objects to import from the module
        from_imports = dict()
        # set of modules to import directly
        direct_imports = set()
        # map from expression classes or expression style ids to their
        # names (abbreviated if there is no  ambiguity, otherwise using 
        # the full address).
        item_names = dict() 
        
        # populate from_imports, direct_imports, and item_names
        for expr_class, constructor in expr_classes_and_constructors:
            class_name = expr_class.__name__
            module_name = self._moduleAbbreviatedName(expr_class.__module__, 
                                                      class_name)
            is_unique = (len(named_items[class_name]) == 1)
            if is_unique:
                from_imports.setdefault(module_name, []).append(constructor)
                item_names[expr_class] = class_name
            else:
                direct_imports.add(module_name)
                item_names[expr_class] = module_name+'.'+constructor
        for namedExprAndStyleId, namedExprAddress in \
                named_subexpr_addresses.items():
            if isinstance(namedExprAddress[0], str):
                # Must be a special expression (axiom, theorem, 
                module_name = namedExprAddress[0] # or common expression)
                item_names[namedExprAndStyleId] = itemName \
                    = namedExprAddress[-1]
                 # Split off '.expr' part if it is a Theorem or Axiom 
                 # KnownTruth
                objName = itemName.split('.')[0]
                module_name = self._moduleAbbreviatedName(module_name, 
                                                          objName)
                is_unique = (len(named_items[itemName]) == 1)
                from_imports.setdefault(module_name, []).append(objName)
            else:
                # Expression must be an attribute of a class
                # (e.g., '_operator_')
                item_names[namedExprAndStyleId] = \
                    (item_names[namedExprAddress[0]] + '.' 
                     + namedExprAddress[1])
                
        # see if we need to add anything to the sys.path
        needs_root_path = False # needs the root of this context added
        needs_local_path = False # needs the local path added
        # first, see if we even need to import a module with the same 
        # root as our context
        root_context = self.context_storage.rootContextStorage.context
        context_root_name = root_context.name
        for module_name in itertools.chain(direct_imports, 
                                           list(from_imports.keys())):
            if module_name.split('.')[0] == context_root_name:
                # If we needed to add a path to sys.path for the
                # directory above the root context, we'll need to do 
                # that explicitly in our expression notebook.
                needs_root_path = root_context._storage.addedPath
                break
            else:
                module = importlib.import_module(module_name)
                if module.__package__ == '':
                    needs_local_path = True
        
        # generate the imports that we need (appending to sys.path
        # if necessary).
        import_stmts = []
        if needs_root_path or needs_local_path:
            # add to the sys path
            import_stmts = ['import sys']
            rel_paths = set()
            if needs_local_path:
                # go up 2 levels, where the local directory is
                rel_paths.add(relurl('.', start=full_hash_dir))
            if needs_root_path:
                # go up enough levels to the context root;
                # 2 levels to get out of the '__pv_it' folder and at 
                # least 1 more to get above the root context.
                rel_paths.add(os.path.join(
                        *(['..']*(self.context.name.count('.')+3))))
            for rel_path in rel_paths:
                import_stmts.append(json.dumps('sys.path.insert(1, "%s")'
                                               %rel_path).strip('"'))
        # direct import statements
        import_stmts += ['import %s'%module_name for module_name
                         in sorted(direct_imports)]
        # from import statements
        import_stmts += ['from %s import '%module_name + 
                         ', '.join(sorted(from_imports[module_name])) for 
                                   module_name in sorted(from_imports.keys())]
        # code to perform the required imports
        import_code = '\\n",\n\t"'.join(import_stmts)
        
        # generate the code for building the expression
        expr_code = ''
        idx = 0
        for sub_expr_and_style_id in multiuse_subexprs:
            sub_expr, sub_expr_style_id = sub_expr_and_style_id
            if hasattr(sub_expr, 'context') and sub_expr.context is not None:
                 # This expression is pulled from a context and does not 
                 # need to be built.
                continue
            idx += 1
            sub_expr_name = 'subExpr%d'%idx
            expr_building_code = self._exprBuildingCode(sub_expr, item_names, 
                                                        isSubExpr=True)
            expr_code += (sub_expr_name + ' = ' + 
                          json.dumps(expr_building_code).strip('"')
                          + '\\n",\n\t"')
            item_names[sub_expr_and_style_id] = sub_expr_name
        expr_building_code = self._exprBuildingCode(expr, item_names, 
                                                    isSubExpr=False)
        expr_code += 'expr = ' + json.dumps(expr_building_code).strip('"')
        
        # link to documentation for the expression's type
        doc_root = os.path.join(proveit_path, '..', '..', 
                                'doc', 'html', 'api')
        class_name = expr.__class__.__name__
        module_name = self._moduleAbbreviatedName(expr.__class__.__module__, 
                                                  class_name)
        doc_file = module_name + '.' + class_name + '.html'
        type_link = relurl(os.path.join(doc_root,doc_file), 
                           start=full_hash_dir)
        
        # expr.ipynb is the default but may change to
        # axiom_expr.ipynb or theorem_expr.ipynb in certain
        # instances.
        filename = 'expr.ipynb'
    
        with open(os.path.join(proveit_path, '..', template_name), 
                  'r') as template:
            nb = template.read()
            if (template_name != '_special_expr_template_.ipynb' 
                    and template_name != '_common_expr_template_.ipynb'):
                nb = nb.replace('#EXPR#', expr_code)
            nb = nb.replace('#IMPORTS#', import_code)
            nb = nb.replace('#CONTEXT#', self.context.name)
            nb = nb.replace('#TYPE#',class_name)
            nb = nb.replace('#TYPE_LINK#', type_link.replace('\\', '\\\\'))
            if (unofficialNameKindContext is not None 
                    or kind is not None):
                kind_str = kind[0].upper() + kind[1:]
                if kind == 'common': kind_str = 'Common Expression'
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#kind#', kind_str.lower())
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = '/'.join(
                        ['..', '..', 
                         Context.specialExprKindToModuleName[kind] + '.ipynb'])
                nb = nb.replace(
                        '#SPECIAL_EXPR_LINK#', 
                        json.dumps(special_expr_link + '#' + name).strip('"'))
            nb = clean_nb(StringIO(nb))
        
        # Write the expression notebook unless it is unchanged.
        if kind == 'axiom':
            filename = 'axiom_expr.ipynb'
        elif kind == 'theorem':
            filename = 'theorem_expr.ipynb'
        alt_filename = 'alt_' + filename
        tmp_filename = 'tmp_' + filename
        filepath = os.path.join(full_hash_dir, filename)
        alt_filepath = os.path.join(full_hash_dir, alt_filename)
        tmp_filepath = os.path.join(full_hash_dir, tmp_filename)
        # Possibly toggle expr.ipynb and alt_expr.ipynb.
        if os.path.isfile(filepath):
            with open(filepath, 'r') as f:
                orig_nb = clean_nb(f)
            if orig_nb != nb:
                if os.path.isfile(alt_filepath):
                    with open(alt_filepath, 'r') as f:
                        orig_alt_nb = clean_nb(f)
                else:
                    orig_alt_nb = None
                if orig_alt_nb == nb:
                    # Just switch expr.ipynb and alt_expr.ipynb.
                    os.replace(filepath, tmp_filepath)
                    os.replace(alt_filepath, filepath)
                    os.rename(tmp_filepath, alt_filepath)
                else:
                    # Replace an existing expr.ipynb
                    if kind is not None:
                        print("%s expression notebook is being updated"
                              %name, template_name)
                        if orig_alt_nb is not None:
                            # Move the original to alt_expr.ipynb.
                            os.replace(filepath, alt_filepath)
                    else:
                        print("Expression notebook is being updated for %s"
                              %str(expr))
                    with open(filepath, 'w') as expr_file:
                        expr_file.write(nb)
        else:
            with open(filepath, 'w') as expr_file:
                expr_file.write(nb)
        
        # if this is a special expression also generate the dependencies 
        # notebook if it does not yet exist
        if template_name == '_special_expr_template_.ipynb':
            dependencies_filename = os.path.join(full_hash_dir, 
                                                 'dependencies.ipynb')
            # Even if the dependencies file exists, write over it since 
            # the expression notebook was rewritten.  This will
            # guarantee the file is overwritten if it needs to be (the
            # name or kind of the special expression changes) and not
            # overwritten if the expression notebook was allowed to
            # remain unchanged.
            dependencies_template_filename = \
                os.path.join(proveit_path, '..', 
                             '_dependencies_template_.ipynb')
            with open(dependencies_template_filename, 'r') as template:
                nb = template.read()
                nb = nb.replace('#IMPORTS#', import_code)
                nb = nb.replace('#CONTEXT#', self.context.name)
                nb = nb.replace('#TYPE#', class_name)
                nb = nb.replace('#TYPE_LINK#', 
                                type_link.replace('\\', '\\\\'))
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = special_expr_link + '#' + name
                nb = nb.replace('#SPECIAL_EXPR_LINK#', 
                                json.dumps(special_expr_link).strip('"'))  
                if kind_str == 'Theorem':
                    see_proof_str = ('***see <a class=\\"ProveItLink\\" '
                                     'href=\\"../../_proofs_/%s.ipynb\\">'
                                     'proof</a>***'%name)
                else: see_proof_str = ''
                nb = nb.replace('#SEE_PROOF#', see_proof_str)
                                
            # Save the dependencies notebook unless it is unchanged.
            if os.path.isfile(dependencies_filename):
                with open(dependencies_filename, 'r') as f:
                    orig_nb = clean_nb(f)
                if orig_nb != nb:                       
                    with open(dependencies_filename, 'w') as dependencies_file:
                        dependencies_file.write(nb)
            else:
                with open(dependencies_filename, 'w') as dependencies_file:
                    dependencies_file.write(nb)
                
            
        # return the relative url to the new proof file
        return relurl(filepath)
        
    def _exprBuildingPrerequisites(
            self, expr, exprClassesAndConstructors, unnamedSubExprOccurences, 
            namedSubExprAddresses, namedItems, can_self_import, isSubExpr=True):
        '''
        Given an Expression object (expr), visit all sub-expressions and
        obtain the set of represented Expression classes (exprClasses), 
        the count for 'unnamed' sub-Expression occurances 
        (unnamedSubExprOccurances as an Expression:int dictionary),
        the 'address' of all named sub-Expressions 
        [namedSubExprAddresses as an Expression:expression-address 
        dictionary], and the Expression(s)/class(es) corresponding
        to each named item (namedItems as a name:set dictionary).  The 
        expression-address is in the form (module, name) for 
        special-expressions or (Expression class, '_operator_') for a 
        Literal operator.  When there are muliple items with the same 
        name, full names must be used instead of abbreviations.
        '''
        from proveit import (Expression, Operation, Literal, ExprTuple, 
                             NamedExprs, ExprArray)
        
        if (isinstance(expr, Literal) and 
                expr in Operation.operationClassOfOperator):
            # the expression is an '_operator_' of an Operation class
            operationClass = Operation.operationClassOfOperator[expr]
            exprClassesAndConstructors.add((operationClass, 
                                            operationClass.__name__))
            namedItems.setdefault(operationClass.__name__, set()).add(
                    operationClass)
            namedSubExprAddresses[(operationClass._operator_, 
                                   operationClass._operator_._style_id)] \
                = (operationClass, '_operator_')
            return
        
        context_folder_storage = \
            ContextFolderStorage.getFolderStorageOfExpr(expr)
        is_active_context_folder = \
            (context_folder_storage == 
             ContextFolderStorage.active_context_folder_storage)
        if (context_folder_storage.folder in ('axioms', 'theorems', 'common')
                and (can_self_import or not is_active_context_folder)):
            # expr may be a special expression from a context.
            try:
                # if it is a special expression in a context, 
                # we want to be able to address it as such.
                expr_id = context_folder_storage._proveItStorageId(expr)
                expr_address = \
                    context_folder_storage.specialExprAddress(expr_id)
            except KeyError:
                expr_address= None
            
            if expr_address is not None:
                namedSubExprAddresses[(expr, expr._style_id)] = \
                    expr_address[1:]
                namedItems.setdefault(expr_address[-1], set()).add(expr)
                return
        
        # add to the unnamed sub-expression count
        unnamedSubExprOccurences[(expr, expr._style_id)] = \
            unnamedSubExprOccurences.get((expr, expr._style_id), 0) + 1
        if unnamedSubExprOccurences[(expr, expr._style_id)] > 1:
            return # already visited this -- no need to reprocess it
        
        if not isSubExpr or expr.__class__ not in (ExprTuple, NamedExprs, 
                                                   ExprArray): 
            # add expr's class to exprClass and named items (unless it
            # is a basic Composite sub-Expression in which case we'll 
            # use a python list or dictionary to represent the composite
            # expression).
            exprClassesAndConstructors.add(
                    (expr.__class__, expr.remakeConstructor()))
            namedItems.setdefault(expr.__class__.__name__, set()).add(
                    expr.__class__)
                                
        # recurse over the expression build arguments
        # (e.g., the sub-Expressions
        for arg in expr.remakeArguments():
            try:
                if isinstance(arg[0], str):
                    # splits into a name, argument pair
                    argname, arg = arg 
            except:
                pass
            if (not isinstance(arg, Expression) and not isinstance(arg, str) 
                    and not isinstance(arg, int)):
                raise TypeError("The arguments of %s.remakeArguments() "
                                "should be Expressions or strings or "
                                "integers: %s instead." 
                                %(str(expr.__class__), str(arg.__class__)))
            if isinstance(arg, Expression):
                subExpr = arg
                self._exprBuildingPrerequisites(
                        subExpr, exprClassesAndConstructors, 
                        unnamedSubExprOccurences, namedSubExprAddresses, 
                        namedItems, can_self_import)
        
    def _moduleAbbreviatedName(self, moduleName, objName):
        '''
        Return the abbreviated module name for the given object based 
        upon the convention that packages will import objects within 
        that package that should be visible externally.  Specifically, 
        this successively checks parent packages to see if the object is
        defined there with the same name.  For example, 
        proveit.logic.boolean.conjunction.and_op will be abbreviated
        to proveit.logic for the 'And' class.
        '''
        module = importlib.import_module(moduleName)
            
        if not os.path.isabs(module.__file__):
            # convert a relative path to a path starting from 
            # the context root
            abs_module_name = self.context.name + '.' + moduleName
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
                if (getattr(cur_module, objName) != 
                        getattr(parent_module, objName)):
                    break
            split_module_name = split_module_name[:-1]
        return '.'.join(split_module_name)
    
    def _exprBuildingCode(self, expr, itemNames, isSubExpr=True):
        from proveit import (Expression, Composite, ExprTuple, 
                             NamedExprs, ExprArray)
                
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
                # either a variable name or code to construct the
                # sub-expression:
                return self._exprBuildingCode(arg, itemNames)
            # see of we can split arg into a (name, value) pair
            try:
                name, val = arg
                if isinstance(name, str):
                    return name + ' = ' + argToString(val)
            except:
                pass
            # the final possibility is that we need a list of 
            # expressions (i.e., parameters of a Lambda expression)
            lst = ', '.join(argToString(argItem) for argItem in arg)
            return '[%s]'%lst
        
        def get_constructor():
            # usually the class name to call the __init__, 
            # but not always
            constructor = expr.remakeConstructor() 
            # may include the module at the front:
            full_class_name = itemNames[expr.__class__] 
            if '.' in full_class_name:
                # prepend the constructor with the module
                # -- assume it is in the same module as the class
                constructor = ('.'.join(full_class_name.split('.')[:-1]) +
                               constructor)
            return constructor
        if isinstance(expr, NamedExprs):
            # convert to (name, value) tuple form
            argStr = ', '.join('(' + argToString(arg).replace(' = ', ',') + ')' 
                               for arg in expr.remakeArguments())                
        else:
            argStr = ', '.join(argToString(arg) for 
                               arg in expr.remakeArguments())                
        withStyleCalls = '.'.join(expr.remakeWithStyleCalls())
        if len(withStyleCalls)>0: withStyleCalls = '.' + withStyleCalls

        if isinstance(expr, Composite):
            if isinstance(expr, ExprTuple):
                compositeStr = argStr
            elif isinstance(expr, ExprArray):
                compositeStr = '{' + argStr.replace(' = ', ':') + '}'                
            else:
                assert isinstance(expr, NamedExprs)
                # list of (name, value) tuples   
                compositeStr = '[' + argStr.replace(' = ', ':') + ']'              
            if isSubExpr and expr.__class__ in (ExprTuple, 
                                                NamedExprs, ExprArray): 
                # It is a sub-Expression and a standard composite class.
                # Just pass it in as an implicit composite expression 
                # (a list or dictionary).
                # The constructor should be equipped to handle it
                # appropriately.
                return ('[' + compositeStr + ']' 
                        if expr.__class__==ExprTuple 
                        else compositeStr)
            else:
                return (get_constructor() + '(' + compositeStr + ')' + 
                        withStyleCalls)
        else:
            return get_constructor() + '(' + argStr + ')' + withStyleCalls
    
    def proofNotebook(self, proof):
        '''
        Return the url to a proof notebook for the given stored proof.
        Create the notebook if necessary.
        '''
        import proveit
        proveit_path = os.path.split(proveit.__file__)[0]
        (context_folder_storage, hash_directory) = self._retrieve(proof)
        filename = os.path.join(context_folder_storage.path, hash_directory, 
                                'proof.ipynb')
        if not os.path.isfile(filename):
            # Copy the template.  Nothing needs to be edited for these.
            template_filename = os.path.join(proveit_path, '..', 
                                             '_proof_template_.ipynb')
            shutil.copyfile(template_filename, filename)
        return relurl(filename)
                    
    def makeExpression(self, exprId):
        '''
        Return the Expression object that is represented in storage by
        the given expression id.
        '''
        import importlib
        # map expression class strings to Expression class objects
        expr_class_map = dict() 
        def importFn(exprClassStr):
            split_expr_class = exprClassStr.split('.')
            module = importlib.import_module('.'.join(split_expr_class[:-1]))
            expr_class_map[exprClassStr] = getattr(
                    module, split_expr_class[-1])
        def exprBuilderFn(exprClassStr, exprInfo, styles, subExpressions):
            expr_class = expr_class_map[exprClassStr]
            expr = expr_class._checked_make(exprInfo, styles, subExpressions)
            return expr
        expr = self._makeExpression(exprId, importFn, exprBuilderFn)
        return expr
        
    def _makeExpression(self, expr_id, importFn, exprBuilderFn):
        '''
        Helper method for makeExpression
        '''
        from proveit import Expression
        from ._dependency_graph import orderedDependencyNodes
        from .context import Context
        # map expr-ids to lists of Expression class string 
        # representations:
        expr_class_strs = dict()
        # relative paths of Expression classes that are local:
        expr_class_rel_strs = dict() 
        core_info_map = dict() # map expr-ids to core information
        styles_map = dict() # map expr-ids to style information
        # map expr-ids to list of sub-expression ids:
        sub_expr_ids_map = dict() 
        # Map the expression storage id to a (context folder storage,
        # hash) tuple.
        exprid_to_storage = dict()
        master_expr_id = expr_id
        try:
            local_context_name = Context().name
        except:
            local_context_name = None
        proveit_obj_to_storage = ContextFolderStorage.proveit_object_to_storage
                
        def getDependentExprIds(expr_id):
            '''
            Given an expression id, yield the ids of all of its 
            sub-expressions.
            '''
            context_name, folder, hash_directory = self._split(expr_id)
            #if hash_directory=='ad618bf3877c30c0b90910432253dfea91e55a040':
            #    print(context_name, folder, hash_directory)
            if context_name != '' and context_name != self.context.name: 
                context = Context.getContext(context_name)
                context_folder_storage = context._contextFolderStorage(folder)
                # Load the "special names" of the context so we
                # will know, for future reference, if this is a special 
                # expression that may be addressed as such.
                context_folder_storage.context_storage.loadSpecialNames()                
            elif folder != self.folder:
                context_folder_storage = \
                    self.context._contextFolderStorage(folder)
            else:
                context_folder_storage = self
            exprid_to_storage[expr_id] = (context_folder_storage,
                                         hash_directory)
            hash_path = self._storagePath(expr_id)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # Extract the unique representation from the pv_it file.
                unique_rep = f.read()
                # Parse the unique_rep to get the expression information.
                (expr_class_str, core_info, style_dict, sub_expr_refs) = \
                    Expression._parse_unique_rep(unique_rep)
                if (local_context_name is not None 
                        and expr_class_str.find(local_context_name) == 0):
                    # import locally if necessary
                    expr_class_rel_strs[expr_id] = \
                        expr_class_str[len(local_context_name)+1:]                
                expr_class_strs[expr_id] = expr_class_str
                # extract the Expression "core information" from the
                # unique representation
                core_info_map[expr_id] = core_info
                styles_map[expr_id] = style_dict
                dependent_refs = sub_expr_refs
                dependent_ids = \
                    self._extractReferencedStorageIds(
                            unique_rep, context_name, folder,
                            storage_ids=dependent_refs)
                sub_expr_ids_map[expr_id] = dependent_ids
                #print('dependent_ids', dependent_ids)
                return dependent_ids
                
        expr_ids = orderedDependencyNodes(expr_id, getDependentExprIds)
        for expr_id in reversed(expr_ids):
            if expr_id in expr_class_rel_strs:
                # there exists a relative path
                try:
                    # First try the absolute path; that is preferred for
                    # consistency sake (we want different imports of 
                    # something to be regarded as the same)
                    importFn(expr_class_strs[expr_id])
                except:
                    # If importing the absolute path fails, maybe the
                    # relative path will work.  This is needed to 
                    # resolve, for example, the issue that the 
                    # proveit.logic package imports from
                    # proveit.logic.boolean._common_ but we need to be
                    # able to execute 
                    # proveit.logic.boolean._common_.ipynb in
                    # the first place which requires imports within 
                    # proveit.logic.boolean.  The solution is to use 
                    # relative imports when executing 
                    # proveit.logic.boolean._common_.ipynb
                    # the first time but afterwards use absolute paths. 
                    importFn(expr_class_rel_strs[expr_id])
                    # use the relative path
                    expr_class_strs[expr_id] = expr_class_rel_strs[expr_id]
            else:
                # there does not exist a relative path; 
                # the absolute path is the only option.
                importFn(expr_class_strs[expr_id])
        # map expr-ids to "built" expressions 
        # (whatever exprBuilderFn returns):
        built_expr_map = dict() 
        for expr_id in reversed(expr_ids):
            sub_expressions =  [built_expr_map[sub_expr_id] for sub_expr_id 
                                in sub_expr_ids_map[expr_id]]
            expr = exprBuilderFn(
                    expr_class_strs[expr_id], core_info_map[expr_id], 
                    styles_map[expr_id], sub_expressions)
            expr_style_id = expr._style_id
            if expr_style_id not in proveit_obj_to_storage:
                # Remember the storage corresponding to the style id
                # for future reference.
                proveit_obj_to_storage[expr_style_id] = \
                    exprid_to_storage[expr_id]
            built_expr_map[expr_id] = expr
        
        return built_expr_map[master_expr_id]        
    
    def makeKnownTruth(self, truth_id):
        '''
        Return the KnownTruth object that is represented in storage by
        the given KnownTruth id.
        '''
        from proveit._core_.known_truth import KnownTruth
        context_name, folder, _ = self._split(truth_id)
        hash_path = self._storagePath(truth_id)
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        exprids = \
            self._extractReferencedStorageIds(unique_rep, context_name, 
                                              folder)
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
        context_name, folder, hash_directory = self._split(proof_id)
        if context_name=='':
            context = self.context
        else:
            context = Context.getContext(context_name)
        context_folder_storage = context._contextFolderStorage(folder)
        hash_path = context_folder_storage._storagePath(proof_id)        
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        # full storage id:
        proof_id = context.name + '.' + folder + '.' + hash_directory 
        proveit_obj_to_storage = ContextFolderStorage.proveit_object_to_storage
        proveit_obj_to_storage[proof_id] = (
                context_folder_storage, hash_directory)   
        return Proof._showProof(context, folder, proof_id, unique_rep)
        
    def recordCommonExprDependencies(self):
        '''
        Record the context names of any reference common expressions in storage
        while creating the common expressions for this context
        (for the purposes of checking for illegal mutual dependencies).
        '''
        from .context import CommonExpressions
        contextNames = CommonExpressions.referenced_contexts
        contextNames = set(contextNames)
        contextNames.discard(self.context.name) # exclude the source context
        if contextNames == self.storedCommonExprDependencies():
            return # unchanged
        referenced_commons_filename = os.path.join(self.pv_it_dir, 'commons',
                                                   'package_dependencies.txt')
        with open(referenced_commons_filename, 'w') as f:
            for context_name in contextNames:
                f.write(context_name + '\n')

    def storedCommonExprDependencies(self):
        '''
        Return the stored set of context names of common expressions
        referenced by the common expression notebook of this context.
        '''
        referenced_commons_filename = os.path.join(self.pv_it_dir, 'commons',
                                                   'package_dependencies.txt')
        if os.path.isfile(referenced_commons_filename):
            with open(referenced_commons_filename, 'r') as f:
                return {line.strip() for line in f.readlines()}
        return set() # empty set by default
        
    def cyclicallyReferencedCommonExprContext(self):
        '''
        Check for illegal cyclic dependencies of common expression
        notebooks.  If there is one, return the name; 
        otherwise return None.
        '''        
        from .context import Context, CommonExpressions
        contextNames = CommonExpressions.referenced_contexts
        referencing_contexts = {contextName:self.context for contextName 
                                in contextNames if contextName != self.name}
        while len(referencing_contexts) > 0:
            contextName, referencing_context = referencing_contexts.popitem()
            context = Context.getContext(contextName)
            if context == self.context:
                # a directly or indirectly referenced context refers 
                # back to the referencing source.
                # cycle found; report context with a common expression 
                # referencing the source
                return referencing_context 
            # extend with indirect references
            new_context_names = context.storedCommonExprDependencies()
            for new_context_name in new_context_names:
                if new_context_name not in referencing_contexts:
                    # add an indirect reference
                    referencing_contexts[new_context_name] = context
        return None
    
    def clean(self, clear=False):
        '''
        Remove all of the hash sub-folders of the 'folder'
        under the directory of this ContextStorage that are
        not currently being referenced via 
        ContextFolderStorage.proveit_obj_to_storage.  
        If 'clear' is True, the entire folder will be removed
        (if possible).
        '''
        if clear:
            try:
                os.remove(self.path)
            except OSError:
                print("Unable to clear '%s'"%self.path)
            return
        
        if self.folder == 'common':
            from proveit import Literal
            # Make sure we reference any literals that are in this
            # context.  First, import the module of the context
            # which should import any modules containing operation
            # classes with _operator_ Literals, then "retreive"
            # Literals of the context as currently references objects.
            importlib.import_module(self.context.name)            
            for literal in Literal.instances.values():
                if literal.context==self.context:
                    self._retrieve(literal)
        currently_referenced = {
                hash_directory for context_folder_storage, hash_directory
                in ContextFolderStorage.proveit_object_to_storage.values() 
                if context_folder_storage==self}
        
        paths_to_remove = list()
        for hash_subfolder in os.listdir(self.path):
            if hash_subfolder == 'name_to_hash.txt': continue
            if hash_subfolder not in currently_referenced:
                hash_folder = os.path.join(self.path, hash_subfolder)
                paths_to_remove.append(hash_folder)
        
        thm_names = set(self.context.theoremNames())
        if self.folder == 'theorems':
            # When 'cleaning' the theorems folder, we will also
            # remove any '_proof_<theorem_name>' folders that are
            # obsolete.
            for _folder in os.listdir(self.pv_it_dir):
                if _folder[:7] == '_proof_':
                    thm_name = _folder[7:]
                    if thm_name not in thm_names:
                        paths_to_remove.append(os.path.join(
                                self.pv_it_dir, _folder))
        
        for hash_folder in paths_to_remove:
            try:
                shutil.rmtree(hash_folder)
            except OSError:
                print("Unable to remove '%s'.\n  Skipping clean step "
                      "(don't worry, it's not critical)."%hash_folder)
    
    def containsAnyExpression(self):
        '''
        Returns True if the __pv_it directory contains any expressions
        based on whether or not there are sub-directories of the __pv_it
        directory other than "_referenced_" after calling "clean()".
        '''
        self.clean()
        for sub_dir in os.listdir(self.pv_it_dir):
            if sub_dir == '_referenced_': 
                continue
            # a sub-directory other than _referenced_; 
            # assume it is for an expression
            return True 
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
            self.context_folder_storage = \
                self.context._contextFolderStorage('axioms')
            hash_dir = self.context._storage.getAxiomHash(name)
        elif kind == 'theorem':
            self.context_folder_storage = \
                self.context._contextFolderStorage('theorems')            
            hash_dir = self.context._storage.getTheoremHash(name)
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")
        self.path = os.path.join(self.context_folder_storage.path, hash_dir)
    
    def __str__(self):
        return self.context.name + '.' + self.name
    
    @staticmethod
    def remove_dependency_proofs(context, kind, hash_folder):
        from .context import Context
        if kind == 'axiom':
            context_folder_storage = \
                context._contextFolderStorage('axioms')
        elif kind == 'theorem':
            context_folder_storage = \
                context._contextFolderStorage('theorems')
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")      
        path = os.path.join(context_folder_storage.path, hash_folder)
        # remove invalidated proofs that use this axiom/theorem
        dependentTheorems = StoredSpecialStmt._readDependentTheorems(path)
        for dependent in dependentTheorems:
            Context.getStoredTheorem(dependent).removeProof()
            
    def readDependentTheorems(self):
        '''
        Return the collection of theorems (as strings) that use this 
        theorem/axiom directly.
        '''
        return StoredSpecialStmt._readDependentTheorems(self.path)
        
    @staticmethod 
    def _readDependentTheorems(path):
        '''
        readDependentTheorems helper.
        '''
        theorems = []
        usedByFilename = os.path.join(path, 'used_by.txt')
        if not os.path.isfile(usedByFilename):
            return theorems # return the empty list
        with open(usedByFilename, 'r') as usedByFile:
            for line in usedByFile:
                theorems.append(line.strip())
        return theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the 
        given theorem or axiom directly or indirectly.
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
        Remove a particular usedByTheorem entry in the used_by.txt for 
        this stored axiom or theorem.
        '''
        self._removeEntryFromFile('used_by.txt', str(usedByTheorem))
    
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
        axioms_notebook_link = relurl(os.path.join(self.context.getPath(), 
                                                   '_axioms_.ipynb'))
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
        return relurl(os.path.join(self.context.getPath(), '_proofs_', 
                                   self.name + '.ipynb'))

    def remove(self, keepPath=False):
        if self.hasProof():
            # must remove the proof first
            self.removeProof()
        StoredSpecialStmt.remove(self, keepPath)

    def readDependencies(self):
        '''
        Returns the used set of axioms and theorems (as a tuple of sets
        of strings) that are used by the given theorem as recorded in 
        the database.
        '''
        usedAxiomNames = set()
        usedTheoremNames = set()
        for usedStmts, usedStmtsFilename in (
                (usedAxiomNames, 'used_axioms.txt'), 
                (usedTheoremNames, 'used_theorems.txt')):
            try:
                with open(os.path.join(self.path, usedStmtsFilename), 
                          'r') as usedStmtsFile:
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
        Return the set of full names of theorems that are presumed 
        directly or indirectly by this one.
        '''
        return self.context._storage.getAllPresumedTheoremNames(self.name)
    
    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  
        Updates dependency links (used_axioms.txt, used_theorems.txt,
        and used_by.txt files) and proven dependency indicators (various
        provenTheorems.txt files  for theorems that depend upon this 
        one) appropriately.
        '''
        from proveit._core_ import Proof
        from .context import Context
              
        # add a reference to the new proof
        active_folder_storage = \
            ContextFolderStorage.active_context_folder_storage
        assert active_folder_storage.folder == '_proof_' + self.name
        proofId = active_folder_storage._proveItStorageId(proof)
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()                    
        # record the proof id
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
        
        usedAxiomNames = [str(usedAxiom) for usedAxiom in proof.usedAxioms()]
        usedTheoremNames = [str(usedTheorem) for usedTheorem 
                            in proof.usedTheorems()]
        
        # Remove usedBy links that are obsolete because the proof has
        # changed
        prevUsedAxiomNames, prevUsedTheoremNames = self.readDependencies()
        for prevUsedAxiom in prevUsedAxiomNames:
            if prevUsedAxiom not in usedAxiomNames:
                Context.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(
                        str(self))
        for prevUsedTheorem in prevUsedTheoremNames:
            if prevUsedTheorem not in usedTheoremNames:
                Context.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(
                        str(self))

        storedUsedAxiomNames = [Context.getStoredAxiom(usedAxiomName) for 
                                usedAxiomName in usedAxiomNames]
        storedUsedTheoremNames = [Context.getStoredTheorem(usedTheoremName) for 
                                  usedTheoremName in usedTheoremNames]
        
        # record axioms/theorems that this theorem directly uses
        for storedUsedStmts, usedStmtsFilename in (
                (storedUsedAxiomNames, 'used_axioms.txt'), 
                (storedUsedTheoremNames, 'used_theorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 
                      'w') as usedStmtsFile:
                for storedUsedStmt in sorted(storedUsedStmts, 
                                             key=lambda stmt:str(stmt)):
                    self.context._storage._includeReference(
                            storedUsedStmt.context)
                    usedStmtsFile.write(str(storedUsedStmt) + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'complete_used_theorems.txt'), 
                  'w') as completedTheoremsFile:
            for usedTheorem in usedTheoremNames:
                if Context.getStoredTheorem(usedTheorem).isComplete():
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the 
        # newly proven theorem
        for storedUsedStmts, prevUsedStmts in (
                (storedUsedAxiomNames, prevUsedAxiomNames), 
                (storedUsedTheoremNames, prevUsedTheoremNames)):
            for storedUsedStmt in storedUsedStmts:
                if str(storedUsedStmt) not in prevUsedStmts: 
                    # (otherwise the link should already exist)
                    with open(os.path.join(storedUsedStmt.path, 'used_by.txt'), 
                              'a') as usedByFile:
                        usedByFile.write(str(self) + '\n')
        
        # if this proof is complete (all of the theorems that it uses 
        # are complete) then  propagate this information to the theorems
        # that depend upon this one.
        self._propagateCompletion()
    
    def hasProof(self):
        '''
        Returns True iff a proof was recorded for this theorem.
        '''
        return os.path.isfile(os.path.join(self.path, 'proof.pv_it'))
    
    def numUsedTheorems(self):
        try:
            return self._countEntries('used_theorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason

    def numCompleteUsedTheorems(self):
        try:
            return self._countEntries('complete_used_theorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason
    
    def isComplete(self):
        '''
        Return True iff this theorem has a proof and all theorems that
        that it uses are also complete.
        '''
        if not self.hasProof():
            # Cannot be complete if there is no proof for this theorem
            return False 
        # If all used theorems have are complete 
        # (and this theorem has a proof), then this theorem is complete.
        return self.numUsedTheorems() == self.numCompleteUsedTheorems()
    
    def _propagateCompletion(self):
        '''
        If this theorem is complete, then let its dependents know.  If
        this update causes a dependent to become complete, propagate the
        news onward.
        '''
        from .context import Context
        if self.isComplete():
            # This theorem has been completely proven.
            # Let the dependents know.
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                storedDependent = Context.getStoredTheorem(dependent)
                _path = os.path.join(storedDependent.path, 
                                    'complete_used_theorems.txt')
                with open(_path, 'a') as f:
                    f.write(str(self) + '\n')
                # propagate this recursively in case self's theorem was 
                # the final  theorem to complete the dependent
                storedDependent._propagateCompletion()
                        
    def removeProof(self):
        '''
        Erase the proof of this theorem from the database and all 
        obsolete links/references.
        '''     
        from .context import Context 
        # was it complete before the proof was removed?
        wasComplete = self.isComplete() 
        # Remove obsolete usedBy links that refer to this theorem by
        # its old proof
        prevUsedAxiomNames, prevUsedTheoremNames = self.readDependencies()
        for usedAxiom in prevUsedAxiomNames:
            Context.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheoremNames:
            Context.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform 
        # dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                stored_thm = Context.getStoredTheorem(dependent)
                stored_thm._undoDependentCompletion(str(self))
        # remove 'proof.pv_it', 'used_axioms.txt', 'used_theorems.txt', 
        # and 'complete_used_theorems.txt' for the theorem
        def removeIfExists(path):
            if os.path.isfile(path): os.remove(path)
        removeIfExists(os.path.join(self.path, 'proof.pv_it'))
        removeIfExists(os.path.join(self.path, 'used_axioms.txt'))
        removeIfExists(os.path.join(self.path, 'used_theorems.txt'))
        removeIfExists(os.path.join(self.path, 'complete_used_theorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or 
        indirectly) by the theorem.  Also, if the given theorem is not 
        completely proven, return the set of unproven theorems that are 
        required (directly or indirectly).  Returns this axiom set and 
        theorem set as a tuple.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to '
                            'obtain its requirements')
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
        Returns the set of names of theorems used to prove the given 
        theorem, directly or indirectly.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to '
                            'obtain its requirements')
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
        Due to the proof being removed, a dependent theorem is no longer
        complete. This new status must be updated and propagated.
        '''
        from .context import Context
        wasComplete = self.isComplete() # was it complete before?
        # remove the entry from complete_used_theorems.txt
        self._removeEntryFromFile('complete_used_theorems.txt', 
                                  usedTheoremName)
        if self.isComplete():
            raise Exception('Corrupt _certified_ database')
        # If this theorem was previously complete before, we need to
        # inform dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                stored_thm = Context.getStoredTheorem(dependent)
                stored_thm._undoDependentCompletion(str(self))


