import hashlib, os
import shutil
import sys
import glob
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

class TheoryStorage:
    '''
    Manages the __pv_it directory of a Theory, the distributed database
    of expressions, axioms, theorems, and proofs.  Additionally manages
    the _sub_theories_.txt file which is in the main directory because
    it should be committed to the repository (unlike the __pv_it
    directory which can all be re-generated).
    '''

    def __init__(self, theory, name, directory, rootDirectory):
        from .theory import Theory, TheoryException
        if not isinstance(theory, Theory):
            raise TheoryException("'theory' should be a Theory object")
        self.theory = theory
        self.name = name
        if rootDirectory is None:
            self.rootTheoryStorage = self
        else:
            self.rootTheoryStorage = Theory(rootDirectory)._storage
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '__pv_it')
        if not os.path.isdir(self.pv_it_dir):
            # make the __pv_it directory
            try:
                os.makedirs(self.pv_it_dir)
            except OSError:
                # maybe another processor beat us to it.
                pass
        
        if self.isRoot():
            # If this is a root theory, let's add the directory above 
            # the root to sys.path if it is needed.
            # try to import the root theory; if it fails, we
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
            
            # set of theory root names that are referenced
            self.referencedTheoryRoots = set()
            # associate the theory name with the directory
            Theory._setRootTheoryPath(name, directory)
            # map theory names to paths for other known root theories
            # in paths.txt
            self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
            if os.path.isfile(self.pathsFilename):
                with open(self.pathsFilename) as pathsFile:
                    for pathLine in pathsFile.readlines():
                        theoryName, path = pathLine.split()
                        if theoryName == '.':
                            if path != directory:
                                # the directory of the theory associated with 
                                # this storage object has changed.
                                self._updatePath()
                        else:
                            Theory._setRootTheoryPath(theoryName, path)
                            self.referencedTheoryRoots.add(theoryName)
            else:
                with open(self.pathsFilename, 'w') as pathsFile:
                    # the first entry indicates the directory of this path
                    pathsFile.write('. ' + directory + '\n')

        # create the _sub_theories_.txt file if it does not already exist
        sub_theories_path = os.path.join(self.directory, '_sub_theories_.txt')
        if not os.path.isfile(sub_theories_path):
            open(sub_theories_path, 'wt').close()
        
        self.subTheoryNames = []
        with open(sub_theories_path, 'rt') as f:
            for k, line in enumerate(f.readlines()):
                self.subTheoryNames.append(line.strip())

        # Map (kind, name) pair to the corresponding special
        # object (Axiom, Theorem, or Expression of a common
        # expression).
        self._kindname_to_objhash = dict()
        
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
        # Base it upon the theory name.
        self._specialExprModules = {kind:self.name+'.%s'%module_name for kind, module_name in Theory.specialExprKindToModuleName.items()}
        
        # Reflects the contents of the 'theorem_dependency_order.txt' file
        # which lists the theorems of the theory in order with other
        # theorems inserted as they are explicitly presumed.
        # Set to None to indicate it must be updated.
        #self._theorem_dependency_order = self._loadTheoremDependencyOrder()
        
        # Map folder names to corresponding TheoryFolderStorage
        # objects.
        self._folder_storage_dict = dict()
        
    def isRoot(self):
        '''
        Return True iff this TheoryStorage is a "root" TheoryStorage 
        (no parent directory with an __init__.py file).
        '''
        return self.rootTheoryStorage is self
                
    def getSubTheoryNames(self):
        '''
        Return the sub-theory names as indicated in the _sub_theories_.txt files.
        '''
        return self.subTheoryNames
        
    def setSubTheoryNames(self, subTheoryNames):
        '''
        Set the sub-theory names listed in the _sub_theories_.txt files.
        '''
        self.subTheoryNames = subTheoryNames
        with open(os.path.join(self.directory, '_sub_theories_.txt'), 'wt') as f:
            for sub_theory_name in self.subTheoryNames:
                f.write(sub_theory_name + '\n')
                
    def appendSubTheoryName(self, subTheoryName):
        '''
        Append the sub-theory name to the _sub_theories_.txt list.
        '''
        with open(os.path.join(self.directory, '_sub_theories_.txt'), 'a') as f:
            f.write(subTheoryName + '\n')
            self.subTheoryNames.append(subTheoryName)
    
    def theoryFolderStorage(self, folder):
        '''
        Return the TheoryFolderStorage object associated with the
        theory of this TheoryStorage and the folder.
        '''
        if folder not in self._folder_storage_dict:
            self._folder_storage_dict[folder] = \
                TheoryFolderStorage(self, folder)
        return self._folder_storage_dict[folder]
    
    def _updatePath(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Theory's.
        '''
        from .theory import Theory
        theory_name = self.name
        # update the local paths.txt
        self._changePath('.', self.directory)
        # update the paths.txt wherever there is a mutual reference
        self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
        with open(self.pathsFilename) as pathsFile:
            for pathLine in pathsFile.readlines():
                theoryName, path = pathLine.split()
                if theoryName != '.':
                    Theory.getTheory(theoryName)._storage._changePath(theory_name, self.directory)
    
    def _changePath(self, movedTheoryName, newPath):
        '''
        Change the path of the movedTheoryName to the newPath.
        '''
        # read in the paths.txt
        with open(self.pathsFilename) as pathsFile:
           prevLines = pathsFile.readlines()
        # re-write the paths.txt with one of the theories' path changed
        with open(self.pathsFilename, 'w') as pathsFile:
            for pathLine in prevLines:
                theoryName, path = pathLine.split()
                if theoryName == movedTheoryName:
                    path = newPath
                pathsFile.write(theoryName + ' ' + path + '\n')

    def _includeReference(self, referencedTheory):
        '''
        Include a path reference from a root Theory to another root 
        Theory via the paths.txt file so the name of the theory
        will be associated with the corresponding directory.
        '''
        root = self.rootTheoryStorage
        referenced_root = referencedTheory._storage.rootTheoryStorage
        if root is not referenced_root:
            referenced_root_name = referenced_root.name
            if referenced_root_name not in self.referencedTheoryRoots:
                with open(self.pathsFilename, 'a') as pathsFile:
                    pathsFile.write(referenced_root_name + ' ' 
                                    + referenced_root.directory + '\n')
                self.referencedTheoryRoots.add(referenced_root_name)
    
    """
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

    def _updateTheoremDependencyOrder(self, theory_theorem_names):
        '''
        Update the information in 'theorem_dependency_order.txt' according to
        the order of the theorems in the theory and the theorems that are
        presumed as indicated by their proof notebooks.
        '''
        ordered_theorems = []
        for theorem_name in theory_theorem_names:
            ordered_theorems += StoredTheorem(self.theory, theorem_name).explicitlyPresumedTheoremNames()
            #ordered_theorems += self.theory.getTheorem(theorem_name).explicitlyPresumedTheoremNames()
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
    """
            
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
        Set the common expressions of the theory.
        '''
        return self.setSpecialExpressions(names, definitions, 'common')

    def setSpecialExpressions(self, names, definitions, kind):
        '''
        Set the common expressions, axioms, or theorems of the theory.
        '''
        from proveit._core_.proof import Axiom, Theorem
        if kind=='common':
            self._common_expr_names = None # force a reload            
        elif kind=='axiom' or kind == 'theorem':
            if kind=='axiom':
                self._axiom_names = None # force a reload
                # Convert definitions from expressions to Axiom Proofs.
                definitions = {name:Axiom(expr, self.theory, name)
                              for name, expr in definitions.items()}
            elif kind == 'theorem':
                self._theorem_names = None # force a reload
                # Convert definitions from expressions to Theorem 
                # Proofs.
                definitions = {name:Theorem(expr, self.theory, name) 
                               for name, expr in definitions.items()}
            # "Retrieve" the proofs to make sure they are stored
            # for future needs.
            theory_folder_storage = self.theoryFolderStorage(
                    kind + 's')
        self._setSpecialObjects(names, definitions, kind)
    
    def _setSpecialObjects(self, names, definitions, kind):
        folder = TheoryStorage._kind_to_folder(kind)
        name_to_hash_file = os.path.join(self.pv_it_dir, folder, 
                                         'name_to_hash.txt')
        theory_name = self.name
        special_hash_ids = self._special_hash_ids[kind] = dict()
        
        # get any previous common expression ids to see if their 
        # reference count needs to be decremented.
        hash_to_old_name = dict() 
        old_name_to_hash = dict()
        orig_lines = []
        if os.path.isfile(name_to_hash_file):
            with open(name_to_hash_file, 'r') as f:
                for line in f.readlines():
                    orig_lines.append(line.rstrip())
                    name, hash_id = line.split()
                    hash_to_old_name[hash_id] = name
                    old_name_to_hash[name] = hash_id
        
        # determine hash ids
        obsolete_hash_ids = set() # for modified statements
        for name in names:
            obj = definitions[name]
            if kind=='common':
                expr = obj
            else:
                expr = obj.provenTruth.expr
            # record the special expression in this theory object
            theory_folder_storage = \
                self.theory._theoryFolderStorage(folder)
            # get the expression id to be stored on 'commons.pv_it'           
            hash_id = theory_folder_storage._proveItStorageId(obj)
            if kind=='common':
                expr_id = hash_id
            else:
                expr_id = theory_folder_storage._proveItStorageId(expr)
            if hash_id in hash_to_old_name:
                if hash_to_old_name[hash_id] != name:
                    print("Renaming %s to %s"%(hash_to_old_name[hash_id],
                                               name))
                # same expression as before
                hash_to_old_name.pop(hash_id)
            special_hash_ids[name] = hash_id
            self._kindname_to_objhash[(kind, name)] = hash_id
            theory_folder_storage._objhash_to_names.setdefault(
                expr_id, []).append(name)
            theory_folder_storage._objhash_to_names.setdefault(
                hash_id, []).append(name)
            if folder != 'common':
                kind = folder[:-1]
                if name not in old_name_to_hash:
                    # added special statement
                    print('Adding %s %s to %s theory'%
                          (kind, name, theory_name))
                elif old_name_to_hash[name] != hash_id:
                    # modified special statement. remove the old one first.
                    print('Modifying %s %s in %s theory'%
                          (kind, name, theory_name))
                    obsolete_hash_ids.add(old_name_to_hash[name])
                # Let's also make sure there is a "used_by"
                # sub-folder.
                used_by_folder = os.path.join(self.pv_it_dir, folder,
                                              hash_id, 'used_by')
                if not os.path.isdir(used_by_folder):
                    try:
                        os.mkdir(used_by_folder)
                    except OSError:
                        pass # no worries
        # Remove proof dependencies of modified statements.
        for hash_id in obsolete_hash_ids:
            if folder == 'theorems':
                # Remove the proof of the modified theorem:
                StoredTheorem(self.theory, name).removeProof()
            if folder != 'common':
                # Remove proofs that depended upon the modified theorem.
                StoredSpecialStmt.remove_dependency_proofs(
                    self.theory, kind, hash_id)
        # Indicate special expression removals.
        for hash_id, name in hash_to_old_name.items():
            if folder == 'common':
                print("Removing %s from %s theory"%
                      (name, theory_name))
            else:
                print("Removing %s %s from %s theory"%
                      (kind, name, theory_name))
                if folder == 'theorems':
                    # Remove the proof of the removed theorem:
                    StoredTheorem(self.theory, name).removeProof()
                # Remove proofs that depended upon the removed theorem.
                StoredSpecialStmt.remove_dependency_proofs(
                    self.theory, kind, hash_id)
        
        # Now we'll write the new name to hash information.
        new_lines = []
        for name in sorted(names):
            new_lines.append(name + ' ' + special_hash_ids[name])
        if new_lines != orig_lines:
            with open(name_to_hash_file, 'w') as f:
                for line in new_lines:
                    f.write(line + '\n')
        
        """
        if kind=='theorem':
            # update the theorem dependency order when setting the
            # theorems
            self._updateTheoremDependencyOrder(names)  
        """

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
        stored for this theory.
        '''
        for kind in ('common', 'axiom', 'theorem'):
            special_hash_ids = self._special_hash_ids[kind]
            if special_hash_ids is None:
                # while the names are read in, the expr id map will 
                # be generated
                list(self._loadSpecialNames(kind))
    
    def _loadCommonExpressionNames(self):
        return self._loadSpecialNames('common')
    
    def _loadSpecialStatementNames(self, kind):
        return self._loadSpecialNames(kind)
        
    def _loadSpecialNames(self, kind):
        '''
        Yield names of axioms/theorems or common expressions
        '''
        folder = TheoryStorage._kind_to_folder(kind)
        theory_folder_storage = self.theoryFolderStorage(folder)
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
                        # unique_rep.pv_it file to get the judgment_id
                        # and then read its uniequ_rep.pv_it to get the
                        # expr_id.
                        storage_id = self.name + '.' + folder + '.' + hash_id
                        for _ in range(2):
                            _theory_folder_storage, hash_folder = \
                                theory_folder_storage._split(storage_id)
                            unique_rep_filename = os.path.join(
                                _theory_folder_storage.path, hash_folder,
                                'unique_rep.pv_it')
                            with open(unique_rep_filename, 'r') as f:
                                rep = f.read()
                            storage_ids = \
                                _theory_folder_storage.\
                                _extractReferencedStorageIds(rep)
                            storage_id = storage_ids[0]
                        expr_id = storage_id
                    self._kindname_to_objhash[(kind, name)] = hash_id
                    theory_folder_storage._objhash_to_names.setdefault(
                        expr_id, []).append(name)
                    theory_folder_storage._objhash_to_names.setdefault(
                        hash_id, []).append(name)
                    yield name
    
    def getAxiomHash(self, name):
        '''
        Return the hash folder where information about the axiom of the 
        given name is stored (stored on the 'axioms' theory storage
        folder).
        '''
        list(self._loadSpecialNames('axiom'))
        try:
            return self._special_hash_ids['axiom'][name]
        except KeyError:
            raise KeyError("%s not found as an axiom in %s"
                           %(name, self.theory.name))
    
    def getTheoremHash(self, name):
        '''
        Return the path where information about the theorem of the given 
        name is stored (stored on the 'theorems' theory storage
        folder).
        '''
        list(self._loadSpecialNames('theorem'))
        try:
            return self._special_hash_ids['theorem'][name]
        except KeyError:
            raise KeyError("%s not found as a theorem in %s"
                           %(name, self.theory.name))
            
    def getCommonExpr(self, name):
        '''
        Return the Expression of the common expression in this theory
        with the given name.
        '''
        expr = self._getSpecialObject('common', name)
        self._loadedCommonExprs[name] = expr
        return expr
    
    def getAxiom(self, name):
        '''
        Return the Axiom of the given name in this theory.
        '''
        if name in self._loadedAxioms:
            return self._loadedAxioms[name]
        axiom = self._getSpecialObject('axiom', name)
        self._loadedAxioms[name] = axiom
        return axiom

    def getTheorem(self, name):
        '''
        Return the Theorem of the given name in this theory.
        '''
        if name in self._loadedTheorems:
            return self._loadedTheorems[name]
        thm = self._getSpecialObject('theorem', name)
        self._loadedTheorems[name] = thm
        return thm
        
    def _getSpecialObject(self, kind, name):
        from proveit._core_.proof import Axiom, Theorem
        from .theory import Theory, UnsetCommonExpressions
        folder = TheoryStorage._kind_to_folder(kind)
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
            
        # set the default Theory in case there is a Literal
        prev_theory_default = Theory.default
        Theory.default = self.theory 
        try:
            theory_folder_storage = self.theoryFolderStorage(folder)
            if (TheoryFolderStorage.owns_active_storage and 
                    theory_folder_storage == TheoryFolderStorage.active_theory_folder_storage):
                # Don't allow anything to be imported from the folder
                # that is currently being generated.
                if kind=='common':
                    raise UnsetCommonExpressions(self.name)
                raise KeyError("Self importing is not allowed")
            obj_id = self._kindname_to_objhash[(kind, name)]
            # make and return expression, axiom, or theorem
            if kind=='common':
                obj = theory_folder_storage.makeExpression(obj_id)
            elif kind=='axiom':
                obj = theory_folder_storage.makeJudgmentOrProof(obj_id)
                if not isinstance(obj, Axiom):
                    raise TypeError("Expecting Axiom, not %s"%obj.__class__)
                assert obj.name == name, "%s not %s as expected"%(obj.name, name)
            elif kind=='theorem':
                obj = theory_folder_storage.makeJudgmentOrProof(obj_id)
                if not isinstance(obj, Theorem):
                    raise TypeError("Expecting Theorem, not %s"%obj.__class__)
                assert obj.name == name, "%s not %s as expected"%(obj.name, name)
            else:
                raise ValueError("'kind' expected to be 'common', 'axiom', or 'theorem'.")
        finally:
            Theory.default = prev_theory_default # reset the default Theory 
        return obj
    
    """
    def getAllPresumedTheoremNames(self, theorem_name):
        '''
        Return the set of full names of presumed theorems that are 
        directly or indirectly presumed by the theorem of the given name
        in this theory.
        '''
        presumed_theorems = set()
        full_theorem_name = self.name + '.' + theorem_name
        self._allPresumedTheoremNames(theorem_name, presumed_theorems, [full_theorem_name])
        return presumed_theorems
    
    def _allPresumedTheoremNames(self, theorem_name, presumed_theorem_names, presumption_chain):
        '''
        Pass back the presumed_theorem_names, a set of full
        names of theorems, that are directly or indirectly presumed
        by the theorem of the given name in this theory.  
        The presumption_chain lists the stack of recursively 
        presumed theorems to check for circular logic.
        '''
        from .theory import Theory
        from .proof import CircularLogicLoop
        if self._theorem_dependency_order is None:
            # The theorem dependency order is stale -- needs to be updated.
            self._updateTheoremDependencyOrder(self.theoremNames()) # update the dependency order first
        idx = self._theorem_dependency_order.index(theorem_name)
        # new presumptions in an external theory as the full theorem name (with theory prefix)
        new_external_presumptions = []
        
        for presumption_name in self._theorem_dependency_order[:idx]:
            if '.' in presumption_name:
                # external presumption
                new_external_presumptions.append(presumption_name)
            else:
                presumed_theorem_names.add(self.name + '.' + presumption_name) # use full name
        
        for presumption_name in new_external_presumptions:
            theory_name, theorem_name = presumption_name.rsplit('.', 1)
            theory = Theory.getTheory(theory_name)
            if theorem_name not in theory.theoremNames():
                raise KeyError("Theorem %s not found in theory %s"%(theorem_name, theory.name))
            if presumption_name in presumption_chain:
                chain_index = presumption_chain.index(presumption_name)
                presumption = theory.getTheorem(theorem_name)
                raise CircularLogicLoop(presumption_chain[chain_index:]+[presumption_name], presumption)
            if presumption_name not in presumed_theorem_names:
                presumed_theorem_names.add(presumption_name)
                theory._storage._allPresumedTheoremNames(theorem_name, presumed_theorem_names, presumption_chain+[presumption_name])
    """

    def thmProofNotebook(self, theorem_name, expr, num_duplicates = 0):
        '''
        Return the relative url to the proof notebook, 
        creating it if it does not already exist.
        num_duplicates is the number of previous instances
        of the expression that we have encountered.
        '''
        proofs_path = os.path.join(self.directory, '_proofs_')
        proof_path = os.path.join(proofs_path, theorem_name)
        # Let's first check if the same expression existed
        # in the previous version -- then we can simply
        # move the proof.
        theory_folder_storage = \
            self.theory._theoryFolderStorage('theorems') 
        expr_id = theory_folder_storage._proveItStorageId(expr)
        expr_id = theory_folder_storage._relative_to_explicit_prefix(expr_id)
        if expr_id in theory_folder_storage._prev_objhash_to_names:
            old_names = theory_folder_storage._prev_objhash_to_names[expr_id]
            if num_duplicates < len(old_names):
                old_name = old_names[num_duplicates]
                if theorem_name != old_name:
                    old_proof_path = os.path.join(proofs_path, old_name)
                    print("Renaming %s to %s"%(old_name, theorem_name))
                    os.rename(old_proof_path, proof_path)
        filename = os.path.join(proof_path, 'thm_proof.ipynb')
        if os.path.isfile(filename):
            # Check the theorem name and make sure it is correct.
            # If not, revise it appropriately.
            existing_theorem_name = self._proofNotebookTheoremName(filename)
            if existing_theorem_name is None:
                # The format is not correct; stash this one and 
                # generate a new one.
                self._stashProof(filename)
            else:
                if existing_theorem_name != theorem_name:
                    # update with the theorem name
                    with open(filename, 'r') as proof_notebook:
                        nb = proof_notebook.read()
                    nb = nb.replace(existing_theorem_name, theorem_name)
                    # remove the file before creating again to force
                    # new capitalization (e.g., in Windows where
                    # capitalization can be flexible)
                    os.remove(filename) 
                    with open(filename, 'w') as proof_notebook:
                        proof_notebook.write(nb)
                return relurl(filename)
        # Check if there is a stashed version of the proof that
        # we can resurrect.
        stashed_versions = glob.glob(proof_path + "~stashed~*")
        if len(stashed_versions) > 0:
            stashed_version = sorted(stashed_versions)[-1]
            print("Resurrecting stashed version of theorem proof notebook: %s"%stashed_version)
            os.rename(stashed_version, proof_path)
            if os.path.isfile(filename):
                return relurl(filename)
        if not os.path.isdir(proof_path):
            # make the directory for the _proofs_
            os.makedirs(proof_path)
        # make a generic 'presumptions.txt' file
        presumptions_filename = os.path.join(proof_path, 'presumptions.txt')
        with open(presumptions_filename, 'w') as _f:
            _f.write(StoredTheorem.PRESUMPTIONS_HEADER + '\n')
            _f.write('proveit\n') # presume all of Prove-It by default
            _f.write(StoredTheorem.PRESUMPTION_EXCLUSION_HEADER + '\n')
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
        # read the template and change the theories as appropriate
        with open(os.path.join(proveit_path, '..', 
                               '_theorem_proof_template_.ipynb'), 
                'r') as template:
            nb = template.read()
            nb = nb.replace('#THEOREM_NAME#', theorem_name)
            theory_links = self.theory.links(
                    os.path.join(self.directory, '_proofs_', theorem_name))
            nb = nb.replace('#THEORY#', theory_links)
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
        for proof_folder in os.listdir(proofs_path):
            if not os.path.isdir(os.path.join(proofs_path, proof_folder)):
                continue # disregard files, just directories
            if proof_folder in theorem_names:
                continue
            proof_path = os.path.join(proofs_path, proof_folder)
            
            if "~stashed~" in proof_folder:
                continue # already a stashed notebook
            
            # may be set to True below if it is a generic notebook
            remove_folder = False 
            
            # next, let's see if this is a generic notebook by 
            # extracting its info, building the generic version, and
            # comparing.
            filename = os.path.join(proof_path, 'thm_proof.ipynb')
            if os.path.isfile(filename):
                theorem_name = self._proofNotebookTheoremName(filename)
                if theorem_name is not None:
                    generic_version = self._generateGenericThmProofNotebook(
                        theorem_name)        
                    with open(filename, 'r') as notebook:
                        if generic_version == notebook.read():
                            # just remove it, it is generic
                            remove_file = True
            
            if remove_folder:
                os.remove(proof_path)
            else:
                self._stashProof(proof_path)
    
    def _stashProof(self, path):
        '''
        Stash a proof path or notebook to a "~stashed~#" 
        file/directory using a '#' (number) that has not been 
        used yet.
        '''
        num = 1
        if path[-len('.ipynb'):] == '.ipynb':
            filename_base = path[:-len('.ipynb')]
            while os.path.isfile(filename_base + "~stashed~%d.ipynb"%num):
                num += 1
            new_path = filename_base + "~stashed~%d.ipynb"%num
        else:
            while os.path.isdir(path + "~stashed~%d"%num):
                num += 1
            new_path = path + "~stashed~%d"%num
        print("Stashing %s to %s in case it is needed."%
              (relurl(path), relurl(new_path)))
        os.rename(path, new_path)

class TheoryFolderStorage:
    # The active theory folder storage (e.g., corresponding to the
    # notebook being executed).
    active_theory_folder_storage = None
    # We may only write expression notebooks to the active storage
    # when it is "owned" and we may not retrieve special expressions
    # from a folder that is "owned" (that would be a self-reference).
    owns_active_storage = False

    # If owns_active_storage is True, this will record
    # all of the hash folders that are legitimately
    # owned.
    owned_hash_folders = set()
    
    # Map style ids of Prove-It object (Expressions, Judgments, and 
    # Proofs) to a (TheoryFolderStorage, hash_id) tuple where it is
    # being stored.
    proveit_object_to_storage = dict()

    clean_nb_method = None
    
    def __init__(self, theory_storage, folder):
        self.theory_storage = theory_storage
        self.theory = theory_storage.theory
        self.pv_it_dir = self.theory_storage.pv_it_dir
        self.folder = folder
        self.path = os.path.join(self.pv_it_dir, folder)
        if not os.path.isdir(self.path):
            # make the folder
            os.makedirs(self.path)

        # For 'common', 'axioms', 'theorems' folders, we map
        # the object hash folder names to the name(s) of the
        # axiom, theorem, or common expression(s).
        self._objhash_to_names = dict()
        # When regenerating common expression, axioms, or
        # theorems, we'll keep track of the previous
        # version.
        self._prev_objhash_to_names = dict()
    
    @staticmethod
    def getFolderStorageOfObj(obj):
        '''
        Obtain the TheoryFolderStorage that 'owns' the given
        expression, or the default TheoryFolderStorage.
        '''
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        if obj._style_id in proveit_obj_to_storage:
            (theory_folder_storage, _) =\
                proveit_obj_to_storage[obj._style_id]
            return theory_folder_storage
        else:
            # Return the "active theory folder storage" as default.
            # This is set by the %begin Prove-It magic command.
            return TheoryFolderStorage.active_theory_folder_storage
    
    def specialExprAddress(self, obj_hash_id):
        '''
        A special expression "address" consists of a kind ('common', 
        'axiom', or 'theorem'), module and the name of the expression.
        Provided that the given expression is one of the special 
        expressions of this theory, return the address as a tuple.
        '''
        kind = TheoryStorage._folder_to_kind(self.folder)
        name = self._objhash_to_names[obj_hash_id][0] # use the first instance.
        if kind == 'axiom' or kind=='theorem':
            name = name + '.expr'
        return kind, self.theory_storage._specialExprModules[kind], name
    
    def unload(self):
        '''
        "Forget" the special objects stored in this folder and
        their sub-expressions to force them to be re-retrieved.
        This is important to do when re-running the notebook
        that generates these objects to be sure the expression
        notebooks all get regenerated (at least checked to see
        if they should change).
        '''
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        to_remove = set()
        for obj_id, (theory_folder_storage, hash_id) \
                in proveit_obj_to_storage.items():
            if theory_folder_storage == self:
                to_remove.add(obj_id)
        for obj_id in to_remove:
            proveit_obj_to_storage.pop(obj_id)
        folder = self.folder
        kind = TheoryStorage._folder_to_kind(folder)
        # Load it before we unload it so we can then
        # store the previous version.
        list(self.theory_storage._loadSpecialNames(kind))
        self._prev_objhash_to_names = dict(self._objhash_to_names)
        for names in self._objhash_to_names.values():
            for name in names:
                self.theory_storage._kindname_to_objhash.pop((kind, name), None)
        self._objhash_to_names.clear()
        if folder=='axioms':
            self.theory_storage._axiom_names = None
            self.theory_storage._loadedAxioms = dict()
        if folder=='theorems':
            self.theory_storage._theorem_names = None
            self.theory_storage._loadedTheorems = dict()
        if folder=='common':
            self.theory_storage._common_exp_names = None
            self.theory_storage._loadedCommonExprs = dict()
        self.theory_storage._special_hash_ids[kind] = None
    
    @staticmethod
    def retrieve_png(expr, latex, configLatexToolFn):
        '''
        Find the expr.png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and relative url where the png is stored as 
        a tuple.
        '''
        theory_folder_storage = \
            TheoryFolderStorage.getFolderStorageOfObj(expr)
        if theory_folder_storage is None:
            raise Exception("You must run the %begin or %proving magic "
                            "command before displaying LaTeX Prove-It "
                            "expressions")
        return theory_folder_storage._retrieve_png(
                expr, latex, configLatexToolFn)
    
    def _retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Helper method of retrieve_png.
        '''
        (theory_folder_storage, hash_directory) = self._retrieve(expr)
        assert theory_folder_storage==self, \
            "How did the theory end up different from expected??"
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
        configLatexToolFn(lt)
        lt.use_breqn = False
        # the 'matplotlib' backend can do some BAD rendering in my 
        # experience (like \lnot rendering as lnot in some theories)
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
                (theory_folder_storage, hash_directory) = \
                    TheoryFolderStorage.proveit_object_to_storage[style_id]
            else:
                (theory_folder_storage, hash_directory) = \
                    self._retrieve(proveItObjectOrId)
            if theory_folder_storage.theory != self.theory:
                theory = theory_folder_storage.theory
                folder = theory_folder_storage.folder
                self.theory_storage._includeReference(theory)
                return theory.name + '.' + folder + '.' + hash_directory
            elif theory_folder_storage.folder != self.folder:
                return theory_folder_storage.folder + '.' + hash_directory                
            else:
                #assert os.path.isdir(os.path.join(self.path, hash_directory))
                return hash_directory
    
    def _split(self, proveItStorageId):
        '''
        Split the given storage-id into a theory name, folder, and 
        the hash directory.  Return the corresponding TheoryFolderStorage
        and hash folder.
        '''
        from proveit._core_.theory import Theory
        if '.' in proveItStorageId:
            # in a different theory or folder
            splitId = proveItStorageId.split('.')
            if len(splitId) == 2:
                folder, hash_folder = splitId[0], splitId[1]
                return self.theory._theoryFolderStorage(folder), hash_folder
            else:
                theory_name, folder, hash_folder = (
                        '.'.join(splitId[:-2]), splitId[-2], splitId[-1])
                theory = Theory.getTheory(theory_name)
                return theory._theoryFolderStorage(folder), hash_folder
        return self, proveItStorageId
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with
        the given storage id.
        '''
        from .theory import Theory
        theory_folder_storage, hash_directory = self._split(proveItStorageId)
        return os.path.join(theory_folder_storage.path, hash_directory)
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It
        object that is dependent upon the style.
        '''
        from proveit import Expression, Judgment, Proof
        prefix = None
        if isinstance(proveItObject, Expression):
            prefix = '' # No prefix for Expressions
        elif isinstance(proveItObject, Judgment):
             # prefix to indicate that it is a Judgment
            prefix = 'Judgment:'
        elif isinstance(proveItObject, Proof):
            prefix = 'Proof:' # prefix to indicate that it is a Proof
        else:
            raise NotImplementedError(
                    'Strorage only implemented for Expressions,'
                    'Judgments, and Proofs')
        # Generate a unique representation using Prove-It object ids for
        # this storage to represent other referenced Prove-It objects.
        return prefix + proveItObject._generate_unique_rep(
                self._proveItStorageId)
    
    def _relative_to_explicit_prefix(self, storage_id):
        # If the exprId is relative to the theory it is in, make the 
        # theory explicit.
        split_id = storage_id.split('.')
        theory_name = self.theory.name
        folder = self.folder
        if len(split_id) == 2:
            return theory_name + '.' + storage_id # explicit folder
        elif len(split_id) == 1:
            # convert local to explicit
            return theory_name + '.' + folder + '.' + storage_id
        else:
            return storage_id # already explicit
    
    def _extractReferencedStorageIds(self, unique_rep, 
                                     storage_ids=None):
        '''
        Given a unique representation string, returns the list of 
        Prove-It storage ids of objects that are referenced.
        These will be 'explicit' ids (e.g., with the full
        theory and folder path).
        '''
        from proveit import Expression, Judgment, Proof, Theory
        if storage_ids is None:
            if unique_rep[:6] == 'Proof:':
                storage_ids = Proof._extractReferencedObjIds(unique_rep[6:])
            elif unique_rep[:9] == 'Judgment:':
                storage_ids = Judgment._extractReferencedObjIds(
                        unique_rep[9:])
            else:
                # Assumed to be an expression then
                storage_ids = Expression._extractReferencedObjIds(unique_rep)
        return [self._relative_to_explicit_prefix(storage_id)
                for storage_id in storage_ids]
    
    def _record_storage(self, obj_style_id, hash_id):
        '''
        Record the object's style id to (theory_folder_storage, hash_id)
        mapping in prove_it_object_to_storage for quick retrieval
        and add the hash_id to the owned_hash_folders as appropriate
        (if it is "owned").
        '''
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        proveit_obj_to_storage[obj_style_id] = (self, hash_id)
        if (TheoryFolderStorage.owns_active_storage and
                self == TheoryFolderStorage.active_theory_folder_storage):
            TheoryFolderStorage.owned_hash_folders.add(hash_id)

    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, Judgment, or 
        Proof.  Create it if it did not previously exist.  Return the 
        (theory_folder_storage, hash_directory) pair where the 
        hash_directory is the directory name (within the theory's
        __pv_it directory) based upon a hash of the unique 
        representation.
        '''
        from proveit import Expression, Literal, Operation
        from proveit._core_.proof import Proof, Axiom, Theorem
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        if proveItObject._style_id in proveit_obj_to_storage:
            return proveit_obj_to_storage[proveItObject._style_id]
        if isinstance(proveItObject, Axiom):
            theory_folder_storage = \
                proveItObject.theory._theoryFolderStorage('axioms')
        elif isinstance(proveItObject, Theorem):
            theory_folder_storage = \
                proveItObject.theory._theoryFolderStorage('theorems')
        elif (isinstance(proveItObject, Literal) and 
                proveItObject in Operation.operationClassOfOperator):
            # _operator_'s of Operations are to be stored in 'common'.
            theory_folder_storage = \
                proveItObject.theory._theoryFolderStorage('common')
        else:
            theory_folder_storage = self
        if theory_folder_storage is not self:
            # Stored in a different folder.
            return theory_folder_storage._retrieve(proveItObject)
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
            self._record_storage(proveItObject._style_id, 
                                 rep_hash + str(index))
            self._generateObjectNotebook(proveItObject)
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
        self._record_storage(proveItObject._style_id, 
                             rep_hash + str(index))
        self._generateObjectNotebook(proveItObject)
        return result

    def _owningNotebook(self):
        '''
        Return the notebook that generates the information in this
        folder.
        '''
        directory = self.theory._storage.directory
        if self.folder in ('common', 'axioms', 'theorems', 'demonstrations'):
            return os.path.join(directory, '_' + self.folder + '_.ipynb')
        thm_proof_prefix = '_proof_'
        if self.folder[:len(thm_proof_prefix)] == '_proof_':
            name = self.folder[len(thm_proof_prefix):]
            return os.path.join(directory, '_proofs_', name, 'thm_proof.ipynb')
        return "the %s notebook in %s"%(self.folder, directory)

    def _raiseNotebookNotFound(self, filepath):
        raise Exception("%s not found.  Rerun %s"%(filepath, self._owningNotebook()))

    def _generateObjectNotebook(self, proveItObject):
        '''
        If this is the active folder storage and the proveItObject
        is an Expression or Proof, generate its notebook.
        '''
        from proveit import Expression, Proof
        # generate the expression or proof notebook as appropriate
        if (TheoryFolderStorage.owns_active_storage and
                self == TheoryFolderStorage.active_theory_folder_storage):
            if isinstance(proveItObject, Expression):
                TheoryFolderStorage.expressionNotebook(proveItObject)
            elif isinstance(proveItObject, Proof):
                self.proofNotebook(proveItObject)

    @staticmethod
    def expressionNotebook(expr, nameKindTheory=None,
                           completeSpecialExprNotebook=False):
        '''
        Return the path of the expression notebook, creating it if it
        does not already exist.  If 'nameKindTheory' is
        provided, it should be the (name, kind, theory) for a special 
        expression that may or may not be complete/official
        (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        import proveit
        from proveit import Expression
        from proveit._core_.proof import Axiom, Theorem
        from .theory import UnsetCommonExpressions
        from json import JSONDecodeError
        proveit_path = os.path.split(proveit.__file__)[0]
        
        if not isinstance(expr, Expression):
            raise ValueError("'expr' should be an Expression object")
        
        if nameKindTheory is not None:
            name, kind, theory = nameKindTheory
        if completeSpecialExprNotebook:
            theory_folder_storage = \
                TheoryFolderStorage.active_theory_folder_storage
        else:
            if nameKindTheory is not None:
                theory_folder_storage = theory._theoryFolderStorage(
                        TheoryStorage._kind_to_folder(kind))
            else:
                theory_folder_storage = \
                    TheoryFolderStorage.getFolderStorageOfObj(expr)
        
        # Determine the kind and name (if it is a "special" expression),
        # and appropriate template to be used.
        if completeSpecialExprNotebook:
            assert nameKindTheory is not None, (
                "Should provide 'nameKindTheory' when completing a "
                "special expression notebook")
            expr_id = theory_folder_storage._proveItStorageId(expr)
            names = theory_folder_storage._objhash_to_names[expr_id]
            if name not in names: 
                raise KeyError("Unable to complete '%s', not found as a "
                               "name for %s."%(name, expr))
            kind = TheoryStorage._folder_to_kind(
                theory_folder_storage.folder)
            if kind=='common':
                template_name = '_common_expr_template_.ipynb'
            else:
                template_name = '_special_expr_template_.ipynb'
        elif nameKindTheory is not None:
            if kind=='common':
                template_name = '_unofficial_common_expr_template_.ipynb'
            else:
                template_name = '_unofficial_special_expr_template_.ipynb'
        else:
            name = kind = None
            template_name = '_expr_template_.ipynb'    

        if completeSpecialExprNotebook:
            assert 'common' in template_name or 'special' in template_name
        # Determine the appropriate hash folder to store the
        # expression notebook in.
        obj = expr
        if kind=='axiom':
            # Store this "special" notebook with the hash for the Axiom.
            obj = Axiom(expr, theory_folder_storage.theory, name)
        elif kind=='theorem':
            # Store this "special" notebook with the hash for the 
            # Theorem.
            obj = Theorem(expr, theory_folder_storage.theory, name)
        obj_theory_folder_storage, hash_directory = \
            theory_folder_storage._retrieve(obj)
        assert obj_theory_folder_storage==theory_folder_storage
        full_hash_dir = os.path.join(theory_folder_storage.path, 
                                     hash_directory)

        if (completeSpecialExprNotebook or (
                TheoryFolderStorage.owns_active_storage and
                theory_folder_storage == 
                TheoryFolderStorage.active_theory_folder_storage)):
            # Only build the notebook in the active folder storage
            nb = theory_folder_storage._buildExpressionNotebook(
                obj, expr, kind, name, full_hash_dir, template_name, 
                nameKindTheory, completeSpecialExprNotebook)
        else:
            nb = None

        # Write the expression notebook unless it is unchanged.
        # expr.ipynb is the default but may change to
        # axiom_expr.ipynb or theorem_expr.ipynb in certain
        # instances.
        filename = 'expr.ipynb'    
        if kind == 'axiom':
            filename = 'axiom_expr.ipynb'
        elif kind == 'theorem':
            filename = 'theorem_expr.ipynb'
        elif kind == 'common':
            filename = 'common_expr.ipynb'
        alt_filename = 'alt_' + filename
        tmp_filename = 'tmp_' + filename
        filepath = os.path.join(full_hash_dir, filename)
        alt_filepath = os.path.join(full_hash_dir, alt_filename)
        tmp_filepath = os.path.join(full_hash_dir, tmp_filename)

        if nb is None:
            # If this isn't the active folder storage,
            # just make sure the file is there and
            # return the link.
            if not os.path.isfile(filepath):
                # disable for now
                #theory_folder_storage._raiseNotebookNotFound(filepath)
                pass
            return relurl(filepath)
        
        #assert False,  '%s'%TheoryFolderStorage.active_theory_folder_storage
        
        # Possibly toggle expr.ipynb and alt_expr.ipynb.
        clean_nb = TheoryFolderStorage._get_clean_nb_method()
        nb = nb.strip()
        if os.path.isfile(filepath):
            with open(filepath, 'r') as f:
                try:
                    orig_nb = clean_nb(f)
                except JSONDecodeError as e:
                    orig_nb = ""
            if orig_nb != nb:
                if os.path.isfile(alt_filepath):
                    with open(alt_filepath, 'r') as f:
                        try:
                            orig_alt_nb = clean_nb(f)
                        except JSONDecodeError as e:
                            orig_alt_nb = ""
                else:
                    orig_alt_nb = None
                #print(len(orig_alt_nb), 'vs', len(nb))
                #print(orig_alt_nb==nb[:len(orig_alt_nb)], print(nb[-1]))
                if orig_alt_nb == nb:
                    # Just switch expr.ipynb and alt_expr.ipynb.
                    os.replace(filepath, tmp_filepath)
                    os.replace(alt_filepath, filepath)
                    os.rename(tmp_filepath, alt_filepath)
                else:
                    # Replace an existing expr.ipynb
                    if kind is not None:
                        print("%s expression notebook is being updated"%name)
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
        # return the relative url to the new proof file
        return relurl(filepath)

    @staticmethod
    def _get_clean_nb_method():
        import proveit
        proveit_path = os.path.split(proveit.__file__)[0]
        if TheoryFolderStorage.clean_nb_method is None:
            # import clean_nb from out nbstripout module (making
            # sure we don't try importing it from an installed 
            # nbstripout if there happens to be one).
            import importlib.util
            import sys
            nbstripout_path = os.path.join(proveit_path, '..', '..', 
                                           'nbstripout', 'nbstripout.py')
            spec = importlib.util.spec_from_file_location('nbstripout', 
                                                         nbstripout_path)
            module = importlib.util.module_from_spec(spec)
            sys.modules['nbstripout'] = module
            spec.loader.exec_module(module)
            from nbstripout import clean_nb
            TheoryFolderStorage.clean_nb_method = clean_nb
        return TheoryFolderStorage.clean_nb_method


    def _buildExpressionNotebook(self, obj, expr, kind, name, full_hash_dir,
                                 template_name, nameKindTheory=None, 
                                 completeSpecialExprNotebook=False):
        '''
        Helper method of expressionNotebook.
        '''
        import proveit
        proveit_path = os.path.split(proveit.__file__)[0]
        from proveit import expressionDepth
        from .theory import Theory
        clean_nb = TheoryFolderStorage._get_clean_nb_method()
                
        expr_classes_and_constructors = set()
        unnamed_subexpr_occurences = dict()
        named_subexpr_addresses = dict()
        # maps each class name or special expression name to a list of 
        # objects being represented; that way we will know whether we 
        # can use the abbreviated name or full address.
        named_items = dict() 
        self._exprBuildingPrerequisites(
                obj, expr_classes_and_constructors, 
                unnamed_subexpr_occurences, named_subexpr_addresses, 
                named_items, 
                can_self_import = completeSpecialExprNotebook,
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
                 # Judgment
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
        needs_root_path = False # needs the root of this theory added
        needs_local_path = False # needs the local path added
        # first, see if we even need to import a module with the same 
        # root as our theory
        root_theory = self.theory_storage.rootTheoryStorage.theory
        theory_root_name = root_theory.name
        for module_name in itertools.chain(direct_imports, 
                                           list(from_imports.keys())):
            if module_name.split('.')[0] == theory_root_name:
                # If we needed to add a path to sys.path for the
                # directory above the root theory, we'll need to do 
                # that explicitly in our expression notebook.
                needs_root_path = root_theory._storage.addedPath
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
                # go up enough levels to the theory root;
                # 2 levels to get out of the '__pv_it' folder and at 
                # least 1 more to get above the root theory.
                rel_paths.add(os.path.join(
                        *(['..']*(self.theory.name.count('.')+3))))
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
            if hasattr(sub_expr, 'theory') and sub_expr.theory is not None:
                 # This expression is pulled from a theory and does not 
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
        
        with open(os.path.join(proveit_path, '..', template_name), 
                  'r') as template:
            nb = template.read()
            if (template_name != '_special_expr_template_.ipynb' 
                    and template_name != '_common_expr_template_.ipynb'):
                nb = nb.replace('#EXPR#', expr_code)
            nb = nb.replace('#IMPORTS#', import_code)
            nb = nb.replace('#THEORY#', self.theory.name)
            nb = nb.replace('#TYPE#',class_name)
            nb = nb.replace('#TYPE_LINK#', type_link.replace('\\', '\\\\'))
            if nameKindTheory is not None:
                kind_str = kind[0].upper() + kind[1:]
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#kind#', kind_str.lower())
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = '/'.join(
                        ['..', '..', '..',
                         Theory.specialExprKindToModuleName[kind] + '.ipynb'])
                nb = nb.replace(
                        '#SPECIAL_EXPR_LINK#', 
                        json.dumps(special_expr_link + '#' + name).strip('"'))
            nb = clean_nb(StringIO(nb))
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
                dep_nb = template.read()
                dep_nb = dep_nb.replace('#IMPORTS#', import_code)
                dep_nb = dep_nb.replace('#THEORY#', self.theory.name)
                dep_nb = dep_nb.replace('#TYPE#', class_name)
                dep_nb = dep_nb.replace('#TYPE_LINK#', 
                                type_link.replace('\\', '\\\\'))
                dep_nb = dep_nb.replace('#KIND#', kind_str)
                dep_nb = dep_nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = special_expr_link + '#' + name
                dep_nb = dep_nb.replace('#SPECIAL_EXPR_LINK#', 
                                json.dumps(special_expr_link).strip('"'))  
                if kind_str == 'Theorem':
                    see_proof_str = ('***see <a class=\\"ProveItLink\\" '
                                     'href=\\"../../../_proofs_/%s/thm_proof.ipynb\\">'
                                     'proof</a>***'%name)
                else: see_proof_str = ''
                dep_nb = dep_nb.replace('#SEE_PROOF#', see_proof_str)
                                
            # Save the dependencies notebook unless it is unchanged.
            if os.path.isfile(dependencies_filename):
                with open(dependencies_filename, 'r') as f:
                    try:
                        orig_nb = clean_nb(f)
                    except JSONDecodeError as e:
                        orig_nb = ""
                if orig_nb != dep_nb:                       
                    with open(dependencies_filename, 'w') as dependencies_file:
                        dependencies_file.write(dep_nb)
            else:
                with open(dependencies_filename, 'w') as dependencies_file:
                    dependencies_file.write(dep_nb)
        
        return nb
        
    def _exprBuildingPrerequisites(
            self, obj, exprClassesAndConstructors, unnamedSubExprOccurences, 
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
                             NamedExprs, ExprArray, Axiom, Theorem)
        
        if isinstance(obj, Axiom) or isinstance(obj, Theorem):
            expr = obj.provenTruth.expr
        else:
            expr = obj
        
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
        
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        theory_folder_storage = \
            TheoryFolderStorage.getFolderStorageOfObj(obj)
        is_active_theory_folder = \
            (theory_folder_storage == 
             TheoryFolderStorage.active_theory_folder_storage)
        if (theory_folder_storage.folder in ('axioms', 'theorems', 'common')
                and (can_self_import or not is_active_theory_folder)):
            # expr may be a special expression from a theory.
            if obj._style_id in proveit_obj_to_storage:
                obj_id = theory_folder_storage._proveItStorageId(obj)
                try:
                    # if it is a special expression in a theory, 
                    # we want to be able to address it as such.
                    expr_address = \
                        theory_folder_storage.specialExprAddress(obj_id)
                    namedSubExprAddresses[(expr, expr._style_id)] = \
                        expr_address[1:]
                    namedItems.setdefault(expr_address[-1], set()).add(expr)
                    return
                except KeyError:
                    pass
        
        # add to the unnamed sub-expression count
        unnamedSubExprOccurences[(expr, expr._style_id)] = \
            unnamedSubExprOccurences.get((expr, expr._style_id), 0) + 1
        if unnamedSubExprOccurences[(expr, expr._style_id)] > 1:
            return # already visited this -- no need to reprocess it
        
        if not isSubExpr or expr.__class__ not in (ExprTuple, NamedExprs): 
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
            # the theory root
            abs_module_name = self.theory.name + '.' + moduleName
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

        if expr.__class__==ExprTuple or expr.__class__==NamedExprs:
            if isinstance(expr, ExprTuple):
                compositeStr = argStr
            else:
                assert isinstance(expr, NamedExprs)
                # list of (name, value) tuples   
                compositeStr = '[' + argStr.replace(' = ', ':') + ']'              
            if isSubExpr and expr.__class__ in (ExprTuple, 
                                                NamedExprs, ExprArray): 
                # It is a sub-Expression and a standard composite class.
                # Just pass it in as an implicit composite expression.
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
        (theory_folder_storage, hash_directory) = self._retrieve(proof)
        filename = os.path.join(theory_folder_storage.path, hash_directory, 
                                'proof.ipynb')
        is_owned_storage = (
            TheoryFolderStorage.owns_active_storage and 
            self == TheoryFolderStorage.active_theory_folder_storage)
        if not os.path.isfile(filename):
            if not is_owned_storage:
                # We can only create the notebook if it is the folder
                # is "owned".
                self._raiseNotebookNotFound(filename)
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
        # Load the "special names" of the theory so we
        # will know, for future reference, if this is a special 
        # expression that may be addressed as such.
        self.theory_storage.loadSpecialNames()                
        expr = self._makeExpression(exprId, importFn, exprBuilderFn)
        return expr
        
    def _makeExpression(self, expr_id, importFn, exprBuilderFn):
        '''
        Helper method for makeExpression
        '''
        from proveit import Expression
        from ._dependency_graph import orderedDependencyNodes
        from .theory import Theory
        # map expr-ids to lists of Expression class string 
        # representations:
        expr_class_strs = dict()
        # relative paths of Expression classes that are local:
        expr_class_rel_strs = dict() 
        core_info_map = dict() # map expr-ids to core information
        styles_map = dict() # map expr-ids to style information
        # map expr-ids to list of sub-expression ids:
        sub_expr_ids_map = dict() 
        # Map the expression storage id to a (theory folder storage,
        # hash) tuple.
        exprid_to_storage = dict()
        master_expr_id = expr_id
        try:
            local_theory_name = Theory().name
        except:
            local_theory_name = None
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
                
        def getDependentExprIds(expr_id):
            '''
            Given an expression id, yield the ids of all of its 
            sub-expressions.
            '''
            theory_folder_storage, hash_directory = self._split(expr_id)
            if theory_folder_storage.theory != self.theory:
                # Load the "special names" of the theory so we
                # will know, for future reference, if this is a special 
                # expression that may be addressed as such.
                theory_folder_storage.theory_storage.loadSpecialNames()                
            exprid_to_storage[expr_id] = (theory_folder_storage,
                                         hash_directory)
            hash_path = self._storagePath(expr_id)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # Extract the unique representation from the pv_it file.
                unique_rep = f.read()
                # Parse the unique_rep to get the expression information.
                (expr_class_str, core_info, style_dict, sub_expr_refs) = \
                    Expression._parse_unique_rep(unique_rep)
                if (local_theory_name is not None 
                        and expr_class_str.find(local_theory_name) == 0):
                    # import locally if necessary
                    expr_class_rel_strs[expr_id] = \
                        expr_class_str[len(local_theory_name)+1:]                
                expr_class_strs[expr_id] = expr_class_str
                # extract the Expression "core information" from the
                # unique representation
                core_info_map[expr_id] = core_info
                styles_map[expr_id] = style_dict
                dependent_refs = sub_expr_refs
                dependent_ids = \
                    theory_folder_storage._extractReferencedStorageIds(
                            unique_rep, storage_ids=dependent_refs)
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
                theory_folder_storage, hash_id = \
                    exprid_to_storage[expr_id]
                theory_folder_storage._record_storage(
                    expr_style_id, hash_id)
            built_expr_map[expr_id] = expr
        
        return built_expr_map[master_expr_id]        
    
    def makeJudgmentOrProof(self, storage_id):
        '''
        Return the Judgment or Proof object that is represented 
        in storage by the given storage_id.
        '''
        from proveit import Theory, Proof, Axiom, Theorem
        from proveit._core_.judgment import Judgment
        theory_folder_storage, hash_folder = self._split(storage_id)
        if theory_folder_storage != self:
            # Make it from the proper TheoryFolderStorage.
            return theory_folder_storage.makeJudgmentOrProof(storage_id)
        theory = self.theory
        hash_path = self._storagePath(storage_id)
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        subids = \
            theory_folder_storage._extractReferencedStorageIds(unique_rep)

        if unique_rep[:6] == 'Proof:':
            kind, full_name = Proof._extractKindAndName(unique_rep)
            theory_name, name = full_name.rsplit('.', 1)
            assert theory_name == self.theory.name
            assert len(subids)==1, (
                "Expected to extract one storage id from %s"
                %unique_rep)
            judgment_id = subids[0]
            if kind=='axiom':
                judgment = self.makeJudgmentOrProof(judgment_id)
                obj = Axiom(judgment.expr, theory, name)
            elif kind=='theorem':
                judgment = self.makeJudgmentOrProof(judgment_id)
                obj = Theorem(judgment.expr, theory, name)
        elif unique_rep[:9] == 'Judgment:':
            truth_expr_id = self.makeExpression(subids[0])
            assumptions = [self.makeExpression(exprid) for exprid in subids[1:]]
            obj = Judgment(truth_expr_id, assumptions)
        theory_folder_storage._record_storage(obj._style_id,
                                               hash_folder)
        return obj
    
    def makeShowProof(self, proof_id):
        '''
        Return the _ShowProof object that mocks up the proof 
        represented in storage by the given proof id for just
        the purposes of displaying the proof.
        '''
        from proveit._core_.proof import Proof
        from proveit._core_.theory import Theory
        theory_folder_storage, hash_directory = self._split(proof_id)
        theory = theory_folder_storage.theory
        folder = theory_folder_storage.folder
        hash_path = theory_folder_storage._storagePath(proof_id)        
        with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
            # extract the unique representation from the pv_it file
            unique_rep = f.read()
        # full storage id:
        proof_id = theory.name + '.' + folder + '.' + hash_directory 
        proveit_obj_to_storage = TheoryFolderStorage.proveit_object_to_storage
        proveit_obj_to_storage[proof_id] = (
                theory_folder_storage, hash_directory)   
        return Proof._showProof(theory, folder, proof_id, unique_rep)
        
    def recordCommonExprDependencies(self):
        '''
        Record the theory names of any reference common expressions in storage
        while creating the common expressions for this theory
        (for the purposes of checking for illegal mutual dependencies).
        '''
        from .theory import CommonExpressions
        theoryNames = CommonExpressions.referenced_theories
        theoryNames = set(theoryNames)
        theoryNames.discard(self.theory.name) # exclude the source theory
        if theoryNames == self.storedCommonExprDependencies():
            return # unchanged
        referenced_commons_filename = os.path.join(self.pv_it_dir, 'commons',
                                                   'package_dependencies.txt')
        with open(referenced_commons_filename, 'w') as f:
            for theory_name in theoryNames:
                f.write(theory_name + '\n')

    def storedCommonExprDependencies(self):
        '''
        Return the stored set of theory names of common expressions
        referenced by the common expression notebook of this theory.
        '''
        referenced_commons_filename = os.path.join(self.pv_it_dir, 'commons',
                                                   'package_dependencies.txt')
        if os.path.isfile(referenced_commons_filename):
            with open(referenced_commons_filename, 'r') as f:
                return {line.strip() for line in f.readlines()}
        return set() # empty set by default
        
    def cyclicallyReferencedCommonExprTheory(self):
        '''
        Check for illegal cyclic dependencies of common expression
        notebooks.  If there is one, return the name; 
        otherwise return None.
        '''        
        from .theory import Theory, CommonExpressions
        theoryNames = CommonExpressions.referenced_theories
        referencing_theories = {theoryName:self.theory for theoryName 
                                in theoryNames if theoryName != self.name}
        while len(referencing_theories) > 0:
            theoryName, referencing_theory = referencing_theories.popitem()
            theory = Theory.getTheory(theoryName)
            if theory == self.theory:
                # a directly or indirectly referenced theory refers 
                # back to the referencing source.
                # cycle found; report theory with a common expression 
                # referencing the source
                return referencing_theory 
            # extend with indirect references
            new_theory_names = theory.storedCommonExprDependencies()
            for new_theory_name in new_theory_names:
                if new_theory_name not in referencing_theories:
                    # add an indirect reference
                    referencing_theories[new_theory_name] = theory
        return None
    
    def clean(self, clear=False):
        '''
        Remove all of the hash sub-folders of the 'folder'
        under the directory of this TheoryStorage that are
        not currently being referenced via 
        TheoryFolderStorage.proveit_obj_to_storage.  
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
            # theory.  First, import the module of the theory
            # which should import any modules containing operation
            # classes with _operator_ Literals, then "retreive"
            # Literals of the theory as currently references objects.
            importlib.import_module(self.theory.name)            
            for literal in Literal.instances.values():
                if literal.theory==self.theory:
                    self._retrieve(literal)

        owned_hash_folders = TheoryFolderStorage.owned_hash_folders
        paths_to_remove = list()
        for hash_subfolder in os.listdir(self.path):
            if hash_subfolder == 'name_to_hash.txt': continue
            if hash_subfolder == 'notebook.css': continue
            hashpath = os.path.join(self.path, hash_subfolder)
            if hash_subfolder not in owned_hash_folders:
                paths_to_remove.append(hashpath)
        
        thm_names = set(self.theory.theoremNames())
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
        def unable_to_remove_warning(name):
            print("Unable to remove %s.\n  Skipping clean step "
                  "(don't worry, it's not critical)"%name)
        if self.folder in ('axioms', 'theorems'):
            # When 'cleaning' the axioms or theorems folder, we will also
            # remove any obsolete 'used_by' folders or 'complete'
            # files.
            for hash_subfolder in os.listdir(self.path):
                if hash_subfolder not in self._objhash_to_names:
                    used_by_path = os.path.join(self.path, hash_subfolder,
                                                'used_by')
                    if os.path.isdir(used_by_path):
                        try:
                            shutil.rmtree(used_by_path)
                        except OSError:
                            unable_to_remove_warning(used_by_path)
                    complete_path = os.path.join(self.path, hash_subfolder,
                                                'complete')
                    if os.path.isfile(complete_path):
                        try:
                            os.remove(complete_path)
                        except OSError:
                            unable_to_remove_warning(complete_path)                            
        
        for hashpath in paths_to_remove:
            try:
                shutil.rmtree(hashpath)
            except OSError:
                unable_to_remove_warning(hashpath)
    
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
    def __init__(self, theory, name, kind):
        '''
        Base class of StoredAxiom and StoredTheorem initialization.
        '''
        self.theory = theory
        self.name = name
        self.kind = kind
        if kind == 'axiom':
            self.theory_folder_storage = \
                self.theory._theoryFolderStorage('axioms')
            hash_dir = self.theory._storage.getAxiomHash(name)
        elif kind == 'theorem':
            self.theory_folder_storage = \
                self.theory._theoryFolderStorage('theorems')            
            hash_dir = self.theory._storage.getTheoremHash(name)
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")
        self.path = os.path.join(self.theory_folder_storage.path, hash_dir)
    
    def __str__(self):
        return self.theory.name + '.' + self.name
    
    @staticmethod
    def remove_dependency_proofs(theory, kind, hash_folder):
        from .theory import Theory
        if kind == 'axiom':
            theory_folder_storage = \
                theory._theoryFolderStorage('axioms')
        elif kind == 'theorem':
            theory_folder_storage = \
                theory._theoryFolderStorage('theorems')
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")      
        path = os.path.join(theory_folder_storage.path, hash_folder)
        # remove invalidated proofs that use this axiom/theorem
        dependentTheorems = StoredSpecialStmt._readDependentTheorems(path)
        for dependent in dependentTheorems:
            try:
                Theory.getStoredTheorem(dependent).removeProof()
            except KeyError:
                # If the dependent is no longer there, we don't need to
                # worry about it (assuming it was removed
                # responsibly with its dependents removed already).
                pass
        removeIfExists(os.path.join(path, 'complete'))
        removeIfExists(os.path.join(path, 'proof.pv_it'))
        removeIfExists(os.path.join(path, 'used_axioms.txt'))
        removeIfExists(os.path.join(path, 'used_theorems.txt'))
            
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
        from .theory import Theory, TheoryException
        theorems = []
        usedByDir = os.path.join(path, 'used_by')
        if not os.path.isdir(usedByDir):
            return theorems # return the empty list
        for filename in os.listdir(usedByDir):
            theorems.append(filename)
        verified_theorems = []
        for theorem in theorems:
            try:
                Theory.getStoredTheorem(theorem)
                verified_theorems.append(theorem)
            except (KeyError, TheoryException):
                # This theorem no longer exists in the database, 
                # apparently.  So we'll remove it from the dependents.
                pass
        to_remove = set(theorems) - set(verified_theorems)
        for obsolete_thm in to_remove:
            try:
                os.remove(os.path.join(usedByDir, filename))
            except OSError:
                pass # no worries
        return verified_theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the 
        given theorem or axiom directly or indirectly.
        '''
        from .theory import Theory
        toProcess = set(self.readDependentTheorems())
        processed = set()
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            processed.add(nextTheorem)
            storedTheorem = Theory.getStoredTheorem(nextTheorem)
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
        filepath = os.path.join(self.path, filename)
        if os.path.isfile(filepath):
            with open(filepath, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line != entryToRemove:
                        remaining.append(line)
        # re-write file with all of the remaining lines
        with open(filepath, 'w') as f:
            for line in remaining:
                f.write(line + '\n')
    
    def _getEntries(self, filename):
        '''
        Returns the entries in a particular file.
        '''
        lines = set()
        with open(os.path.join(self.path, filename), 'r') as f:
            for line in f:
                lines.add(line)
        return lines

    def _countEntries(self, filename):
        '''
        Returns the number of unique entries in a particular file.
        '''
        return len(self._getEntries(filename))

    def _removeUsedByEntry(self, usedByTheorem):
        '''
        Remove a particular usedByTheorem entry in the used_by folder of 
        this stored axiom or theorem.
        '''
        usedByDir = os.path.join(self.path, 'used_by')
        try:
            os.remove(os.path.join(usedByDir, usedByTheorem))
        except OSError:
            pass # no worries        
    
class StoredAxiom(StoredSpecialStmt):
    def __init__(self, theory, name):
        '''
        Creates a StoredAxioms object for managing an axioms's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, theory, name, 'axiom')
    
    def getDefLink(self):
        '''
        Return the link to the axiom definition in the _axioms_ notebook.
        '''
        axioms_notebook_link = relurl(os.path.join(self.theory.getPath(), 
                                                   '_axioms_.ipynb'))
        return axioms_notebook_link + '#' + self.name

def removeIfExists(path):
    if os.path.isfile(path): 
        os.remove(path)

class StoredTheorem(StoredSpecialStmt):
    PRESUMPTIONS_HEADER = '# THEOREMS AND THEORIES THAT MAY BE PRESUMED:'
    PRESUMPTION_EXCLUSION_HEADER = '# THEOREMS AND THEORIES TO EXCLUDE:'
    
    def __init__(self, theory, name):
        '''
        Creates a StoredTheorem object for managing a theorem's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, theory, name, 'theorem')

    def getProofLink(self):
        '''
        Return the link to the theorem's proof notebook.
        '''
        return relurl(os.path.join(self.theory.getPath(), '_proofs_', 
                                   self.name, 'thm_proof.ipynb'))
        

    def remove(self, keepPath=False):
        if self.hasProof():
            # must remove the proof first
            self.removeProof()
        StoredSpecialStmt.remove(self, keepPath)

    def readUsedAxioms(self):
        '''
        Return the recorded list of axioms.
        '''
        return list(self._readUsedStmts('axioms'))
        
    def readUsedTheorems(self):
        '''
        Return the recorded list of theorems.
        '''
        return list(self._readUsedStmts('theorems'))

    def _readUsedStmts(self, kind):
        '''
        Returns the used set of axioms and theorems (as a tuple of sets
        of strings) that are used by the given theorem as recorded in 
        the database.
        '''
        try:
            with open(os.path.join(self.path, 'used_%s.txt'%kind), 
                      'r') as usedStmtsFile:
                for line in usedStmtsFile:
                    line = line.strip()
                    yield line
        except IOError:
            pass # no contribution if the file doesn't exist
    
    """
    def recordPresumedTheories(self, presumed_theory_names):
        '''
        Record information about what other theories are
        presumed in the proof of this theorem.
        '''
        from .theory import Theory
        for presumed_theory in presumed_theory_names:
            # raises an exception if the theory is not known
            Theory.getTheory(presumed_theory) 
        presuming_str = '\n'.join(presumed_theory_names) + '\n'
        presuming_file = os.path.join(self.path, 'presumed_theories.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                if presuming_str == f.read():
                    return # unchanged; don't need to record anything
        with open(presuming_file, 'w') as f:
            f.write(presuming_str)

    def presumedTheories(self):
        '''
        Return the list of presumed theories.
        '''
        # first read in the presuming info
        presumptions = []
        presuming_file = os.path.join(self.path, 'presumed_theories.txt')
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
        
        # The theory's theorem dependency order is now stale
        # and needs to be updated:
        self.theory._storage.invalidateTheoremDependencyOrder()
    
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
    
    """
    def getRecursivelyPresumedTheorems(self, presumed_theorems, presumption_chain=None):
        '''
        Append presumed theorem objects to 'presumed_theorems'.
        For each theorem, do this recursively.
        presumption_chain is used internally to detect and reveal
        circular dependencies.
        '''
        from .theory import Theory
        from .proof import CircularLogicLoop
        # first get the directly presumed theorems
        presumptions = self.directlyPresumedTheorems()
        if presumption_chain is None:
            presumption_chain = [str(self)]
        else:
            presumption_chain.append(str(self))
        # Iterate through each presuming string and add it as
        # a theory name or a theorem.  For theorem's, recursively
        # add the presuming information.
        for presumption in presumptions:
            if not isinstance(presumption, str):
                raise ValueError("'presumptions' should be a collection of strings for theory names and/or full theorem names")
            theory_name, theorem_name = presumption.rsplit('.', 1)
            thm = Theory.getTheory(theory_name).getTheorem(theorem_name)
            if str(thm) in presumption_chain:
                index = presumption_chain.index(str(thm))
                raise CircularLogicLoop(presumption_chain[index:]+[str(thm)], thm)
            # add the theorem and anything presumed by that theorem to the set of presumed theorems/theories
            if thm not in presumed_theorems:
                presumed_theorems.add(thm)
                thm._storedTheorem().getRecursivelyPresumedTheorems(presumed_theorems, list(presumption_chain))
    """
    """
    def getAllPresumedTheoremNames(self):
        '''
        Return the set of full names of theorems that are presumed 
        directly or indirectly by this one.
        '''
        return self.theory._storage.getAllPresumedTheoremNames(self.name)
    """
    
    def getPresumptionsAndExclusions(self):
        '''
        Return the set of theorems and theories that are explicitly
        presumed by this theorem, and a set of exclusions (e.g.,
        you could presume the proveit.logic theory but exclude
        proveit.logic.equality).
        '''
        proof_path = os.path.join(self.theory.getPath(), 
                                  '_proofs_', self.name)

        presumptions = set()
        exclusions = set()
        presumptions_filename = os.path.join(proof_path, 'presumptions.txt')
        
        # Let's create the generic version.
        # TODO: remove
        if not os.path.isdir(proof_path):
            os.mkdir(proof_path)
        if not os.path.isfile(presumptions_filename):            
            with open(presumptions_filename, 'w') as f:
                f.write(StoredTheorem.PRESUMPTIONS_HEADER + '\n')
                f.write('proveit\n')
                f.write(StoredTheorem.PRESUMPTION_EXCLUSION_HEADER + '\n')
        
        active = presumptions
        top_header = StoredTheorem.PRESUMPTIONS_HEADER
        exclusions_header = StoredTheorem.PRESUMPTION_EXCLUSION_HEADER
        with open(presumptions_filename, 'r') as f:
            for line in f.readlines():
                line = line.strip()
                if line[0] == '#':
                    if line == exclusions_header:
                        active = exclusions
                    elif line != top_header:
                        raise Exception("%s file is not in a valid format. "
                                        "%s does not match %s or %s."
                                        %(presumptions_filename, line,
                                          top_header, exclusions_header))
                elif line[0] != '#':
                    active.add(line)
        return presumptions, exclusions
    
    def _recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  
        Updates dependency links (used_axioms.txt, used_theorems.txt
        files and used_by folder) and completion markers appropriately
        (empty 'complete' files).  Also, record the presumptions
        that were actually used in a presumptions.txt file.
        '''
        from proveit._core_ import Proof
        from .theory import Theory
              
        # add a reference to the new proof
        active_folder_storage = \
            TheoryFolderStorage.active_theory_folder_storage
        assert active_folder_storage.folder == '_proof_' + self.name
        active_folder_storage._retrieve(proof)
        proofId = self.theory_folder_storage._proveItStorageId(proof)
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
        prevUsedAxiomNames, prevUsedTheoremNames = (
                self.readUsedAxioms(), self.readUsedTheorems())
        for prevUsedAxiom in prevUsedAxiomNames:
            if prevUsedAxiom not in usedAxiomNames:
                try:
                    Theory.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(
                            str(self))
                except KeyError:
                    pass # don't worry if it has alread been removed
        for prevUsedTheorem in prevUsedTheoremNames:
            if prevUsedTheorem not in usedTheoremNames:
                try:
                    Theory.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(
                            str(self))
                except KeyError:
                    pass # don't worry if it has alread been removed

        storedUsedAxiomNames = [Theory.getStoredAxiom(usedAxiomName) for 
                                usedAxiomName in usedAxiomNames]
        storedUsedTheoremNames = [Theory.getStoredTheorem(usedTheoremName) for 
                                  usedTheoremName in usedTheoremNames]
        
        # record axioms/theorems that this theorem directly uses
        for storedUsedStmts, usedStmtsFilename in (
                (storedUsedAxiomNames, 'used_axioms.txt'), 
                (storedUsedTheoremNames, 'used_theorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 
                      'w') as usedStmtsFile:
                for storedUsedStmt in sorted(storedUsedStmts, 
                                             key=lambda stmt:str(stmt)):
                    self.theory._storage._includeReference(
                            storedUsedStmt.theory)
                    usedStmtsFile.write(str(storedUsedStmt) + '\n')
        
        # for each used axiom/theorem, record that it is used by the 
        # newly proven theorem
        for storedUsedStmts, prevUsedStmts in (
                (storedUsedAxiomNames, prevUsedAxiomNames), 
                (storedUsedTheoremNames, prevUsedTheoremNames)):
            for storedUsedStmt in storedUsedStmts:
                if str(storedUsedStmt) not in prevUsedStmts: 
                    # (otherwise the link should already exist)
                    open(os.path.join(storedUsedStmt.path, 'used_by',
                                      str(self)), 'w')
        
        # If this proof is complete (all of the theorems that it uses 
        # are complete) then  propagate this information to the theorems
        # that depend upon this one.
        self._propagateCompletion()
    
        # Record any imported theorem that is usable as a "presumptions"
        # stored in a presumptions.txt file that should be allowable 
        # theorems whenever the proof is regenerated.
        proof_path = os.path.join(self.theory.getPath(), 
                                  '_proofs_', self.name)
        
        # For temporary backward compatibility, created the directory
        # if necessary.  TODO: remove
        if not os.path.isdir(proof_path):
            os.mkdir(proof_path)
        
        '''
        # This is too specific and results in error during automation.
        # With future work, maybe we can use this approach, but it's
        # too much work right now and it isn't clear if it is very
        # doable.
        with open(os.path.join(proof_path, 'presumptions.txt'), 'w') as f:
            for theorem in proof.usedTheorems():
            #for theorem in Theorem.allTheorems:
                #if theorem.isUsable():
                f.write(str(theorem) + '\n')
        '''
        
        from proveit._core_.proof import Theorem
        with open(os.path.join(proof_path, 'presumptions.txt'), 'w') as f:
            f.write(StoredTheorem.PRESUMPTIONS_HEADER + '\n')
            usable_theorem_names = [str(theorem) for theorem 
                                    in Theorem.allTheorems 
                                    if theorem.isUsable()]
            for theorem in sorted(usable_theorem_names):
                f.write(str(theorem) + '\n')
            f.write(StoredTheorem.PRESUMPTION_EXCLUSION_HEADER + '\n')
    
    def hasProof(self):
        '''
        Returns True iff a proof was recorded for this theorem.
        '''
        return os.path.isfile(os.path.join(self.path, 'proof.pv_it'))
        
    def isComplete(self):
        '''
        Return True iff this theorem has a proof and all theorems that
        that it uses are also complete.
        '''
        # An empty file named "complete" is used to indicate that
        # a proof is complete.
        return os.path.isfile(os.path.join(self.path, 'complete'))
    
    def _propagateCompletion(self):
        '''
        If this theorem is complete, then let its dependents know.  If
        this update causes a dependent to become complete, propagate the
        news onward.
        '''
        from .theory import Theory
        self._markIfComplete()
        if self.isComplete():
            # This theorem has been completely proven.
            # Let the dependents know.
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                try:
                    storedDependent = Theory.getStoredTheorem(dependent)
                except KeyError:
                    # Dependent was removed; skip it.
                    continue
                # propagate this recursively in case self's theorem was 
                # the final  theorem to complete the dependent
                storedDependent._propagateCompletion()
    
    def _markIfComplete(self):
        '''
        If all of the used theorems are complete, this is now complete.
        '''
        from .theory import Theory
        if all(Theory.getStoredTheorem(used_theorem).isComplete() for 
               used_theorem in self.readUsedTheorems()):
            # An empty 'complete' file marks the completion.
            open(os.path.join(self.path, 'complete'), 'w')
    
    def removeProof(self):
        '''
        Erase the proof of this theorem from the database and all 
        obsolete links/references.
        '''     
        from .theory import Theory 
        # Remove obsolete used-by links that refer to this theorem by
        # its old proof.
        prevUsedAxiomNames, prevUsedTheoremNames = (
                self.readUsedAxioms(), self.readUsedTheorems())
        for usedAxiom in prevUsedAxiomNames:
            try:
                Theory.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
            except KeyError:
                pass # If it doesn't exist, never mind.
        for usedTheorem in prevUsedTheoremNames:
            try:
                Theory.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
            except KeyError:
                pass # If it doesn't exist, never mind.
        # If it was previously complete before, we need to erase the
        # completion marker and inform dependents that it is not longer 
        # complete.
        self._undoDependentCompletion()
        # remove 'proof.pv_it', 'used_axioms.txt', 'used_theorems.txt', 
        removeIfExists(os.path.join(self.path, 'proof.pv_it'))
        removeIfExists(os.path.join(self.path, 'used_axioms.txt'))
        removeIfExists(os.path.join(self.path, 'used_theorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or 
        indirectly) by the theorem.  Also, if the given theorem is not 
        completely proven, return the set of unproven theorems that are 
        required (directly or indirectly).  Returns this axiom set and 
        theorem set as a tuple.
        '''
        from .theory import Theory
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to '
                            'obtain its requirements')
        usedAxiomNames, usedTheoremNames = (
                self.readUsedAxioms(), self.readUsedTheorems())
        requiredAxioms = set(usedAxiomNames) # just a start
        requiredTheorems = set()
        processed = set()
        toProcess = set(usedTheoremNames)
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            storedTheorem = Theory.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                requiredTheorems.add(nextTheorem)
                processed.add(nextTheorem)
                continue
            usedAxiomNames, usedTheoremNames = (
                    storedTheorem.readUsedAxioms(), 
                    storedTheorem.readUsedTheorems())
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
        from .theory import Theory
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to '
                            'obtain its requirements')
        usedTheoremNames = self.readUsedTheorems()
        allUsedTheoremNames = set()
        processed = set()
        toProcess = set(usedTheoremNames)
        while len(toProcess) > 0:
            nextTheoremName = toProcess.pop()
            allUsedTheoremNames.add(nextTheoremName)
            storedTheorem = Theory.getStoredTheorem(nextTheoremName)
            if not storedTheorem.hasProof():
                processed.add(nextTheoremName)
                continue
            usedTheoremNames = storedTheorem.readUsedTheorems()
            for usedTheoremName in usedTheoremNames:
                if usedTheoremName not in processed:
                    toProcess.add(usedTheoremName)
            processed.add(nextTheoremName)
        return allUsedTheoremNames 

    def _undoDependentCompletion(self):
        '''
        Due to the proof being removed, a dependent theorem is no longer
        complete. This new status must be updated and propagated.
        '''
        from .theory import Theory
        wasComplete = self.isComplete() # was it complete before?
        # Remove the 'complete' file indicating that it was no longer
        # complete.
        removeIfExists(os.path.join(self.path, 'complete'))
        # If this theorem was previously complete before, we need to
        # inform dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                stored_thm = Theory.getStoredTheorem(dependent)
                stored_thm._undoDependentCompletion()


