import hashlib, os
import shutil

class Storage:
    '''
    Manages the _pv_it_ directory of a Context, the distributed database
    of expressions, axioms, theorems, and proofs.
    '''
    
    def __init__(self, context, directory):
        from context import Context, ContextException
        if not isinstance(context, Context):
            raise ContextException("'context' should be a Context object")
        self.context = context
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '_pv_it_')
        if not os.path.isdir(self.pv_it_dir):
            # make the directory for the storage
            os.makedirs(self.pv_it_dir)
        
        if self.context.isRoot():
            # set of context root names that are referenced
            self.referencedContextRoots = set()
            # associate the context name with the directory
            Context.setRootContextPath(context.name, directory)
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
                            Context.setRootContextPath(contextName, path)
                            self.referencedContextRoots.add(contextName)
            else:
                with open(self.pathsFilename, 'w') as pathsFile:
                    # the first entry indicates the directory of this path
                    pathsFile.write('. ' + directory + '\n')
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    def _updatePath(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Context's.
        '''
        from context import Context
        myContextName = self.context.name
        # update the local paths.txt
        self._changePath('.', self.directory)
        # update the paths.txt wherever there is a mutual reference
        self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
        with open(self.pathsFilename) as pathsFile:
            for pathLine in pathsFile.readlines():
                contextName, path = pathLine.split()
                if contextName != '.':
                    Context.getContext(contextName)._storage._changePath(myContextName, self.directory)
    
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
        
    def includeReference(self, otherStorage):
        '''
        Include a path reference from a root Context to another root Context,
        both in the referencedContextRoots set and in the paths.txt file. 
        '''
        otherContextName = otherStorage.context.name
        if otherContextName not in self.referencedContextRoots:
            with open(self.pathsFilename, 'a') as pathsFile:
                pathsFile.write(otherContextName + ' ' + otherStorage.directory + '\n')
            self.referencedContextRoots.add(otherContextName)
        
    def retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Find the expr.png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and path where the png is stored as a tuple.
        '''
        if hasattr(expr, 'context') and expr.context != self.context:
            return expr.context._stored_png(expr, latex, configLatexToolFn)
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
                            return png_file.read(), png_path
        # store the latex string in the latex file
        with open(latex_path, 'wb') as latex_file:
            latex_file.write(latex)
        # generate, store and return the png file
        png = self._generate_png(latex, configLatexToolFn)
        with open(png_path, 'wb') as png_file:
            png_file.write(png)
        return png, png_path
    
    def _generate_png(self, latex, configLatexToolFn):
        '''
        Generate the png image for the given latex using the given latex
        configuration function.
        '''
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        png = latex_to_png(latex, backend='dvipng', wrap=True)
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
            (context, hash_directory) = self._retrieve(proveItObjectOrId)
            if context != self.context:
                self.context._includeMutualReferences(context)
                return context.name + '.' + hash_directory
            else:
                return hash_directory
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with the given
        storage id.
        '''
        from context import Context
        if '.' in proveItStorageId:
            # in a different context
            splitId = proveItStorageId.split('.')
            context_name, hash_directory = '.'.join(splitId[:-1]), splitId[-1]
            pv_it_dir = Context.getContext(context_name)._storage.pv_it_dir
            return os.path.join(pv_it_dir, hash_directory)
        return os.path.join(self.context._storage.pv_it_dir, proveItStorageId)
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It object.
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
    
    def _extractReferencedStorageIds(self, unique_rep):
        '''
        Given a unique representation string, returns the list of Prove-It
        storage ids of objects that are referenced.
        '''
        from proveit import Expression, KnownTruth, Proof
        if unique_rep[:6] == 'Proof:':
            return Proof._extractReferencedObjIds(unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            return KnownTruth._extractReferencedObjIds(unique_rep[11:])
        else:
            # Assumed to be an expression then
            return Expression._extractReferencedObjIds(unique_rep)

    def _addReference(self, proveItStorageId):
        '''
        Increment the reference count of the prove-it object with the given
        storage identifier.  The ref_count.txt file is updated with the new 
        reference count.
        '''        
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
           
    def _removeReference(self, proveItStorageId):
        '''
        Decrement the reference count of the prove-it object with the given
        storage identifier.  If the reference count goes down to zero, then
        the files storing this prove-it object's data will be deleted
        (and the directory if nothing else is in it).  Otherwise, the
        ref_count.txt file is simply updated with the new reference count.
        '''
        hash_path = self._storagePath(proveItStorageId)
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            refCount = int(f.read().strip()) - 1
        if refCount <= 0:
            # Reference count down to zero (or less).  Remove references to
            # referenced objects and then delete this prove-it object from
            # storage and everything associated with it.
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                rep = f.read()
            for objId in self._extractReferencedStorageIds(rep):
                self._removeReference(objId)
            # remove the entire directory storing this prove-it object
            os.rmdir(hash_path)
        else:
            # change the reference count in the file
            with open(os.path.join(hash_path, 'ref_count.txt'), 'w') as f:
                f.write(str(refCount)+'\n')
    
    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the (context, hash_directory)
        pair, where the hash_directory is the directory name (within the context's
        _pv_it_ directory) based upon a hash of the unique representation.
        '''
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        if hasattr(proveItObject, 'context') and proveItObject.context != self.context:
            # stored in a different context
            return proveItObject.context._storage._retrieve(proveItObject)
        pv_it_dir = self.pv_it_dir
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        if not os.path.exists(pv_it_dir):
            os.mkdir(pv_it_dir)
        hash_path = os.path.join(pv_it_dir, rep_hash)
        # append the hash value with an index, avoiding collisions (that should
        # be astronomically rare, but let's not risk it).
        index = 0
        while os.path.exists(hash_path + str(index)):
            indexed_hash_path = hash_path + str(index)
            with open(os.path.join(indexed_hash_path, 'unique_rep.pv_it'), 'r') as f:
                rep = f.read()
                if rep == unique_rep: # found a match; it is already in storage
                    # remember this for next time
                    result = (self.context, rep_hash+str(index))
                    self._proveItObjects[proveItObject] = result
                    return result
            index += 1
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
        result = (self.context, rep_hash+str(index))
        self._proveItObjects[proveItObject] = result
        if not hasattr(proveItObject, 'context'):
            proveItObject.context = self.context # note the context where it is stored
        return result
    
    def makeExpression(self, exprId):
        import importlib
        exprClassMap = dict() # map expression class strings to Expression class objects
        def importFn(exprClassStr):
            splitExprClass = exprClassStr.split('.')
            module = importlib.import_module('.'.join(splitExprClass[:-1]))
            exprClassMap[exprClassStr] = getattr(module, splitExprClass[-1])
        def exprBuilderFn(exprClassStr, exprInfo, subExpressions):
            return exprClassMap[exprClassStr].make(exprInfo, subExpressions)
        return self._makeExpression(exprId, importFn, exprBuilderFn)
    
    def _makeExpression(self, exprId, importFn, exprBuilderFn):
        from proveit import Expression
        from _dependency_graph import orderedDependencyNodes
        exprClassStrs = dict() # map expr-ids to Expression class string representations
        coreInfoMap = dict() # map expr-ids to core information
        subExprIdsMap = dict() # map expr-ids to list of sub-expression ids 
        masterExprId = exprId
        def getSubExprIds(exprId):
            hash_path = self._storagePath(exprId)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # extract the unique representation from the pv_it file
                unique_rep = f.read()
                # extract the Expression class from the unique representation 
                exprClassStrs[exprId] = Expression._extractExprClass(unique_rep)
                # extract the Expression "core information" from the unique representation
                coreInfoMap[exprId] = Expression._extractCoreInfo(unique_rep)
                # get the sub-expressions all sub-expressions
                subExprIdsMap[exprId] = Expression._extractReferencedObjIds(unique_rep)
                return subExprIdsMap[exprId]
        exprIds = orderedDependencyNodes(exprId, getSubExprIds)
        for exprId in reversed(exprIds):
            importFn(exprClassStrs[exprId])
        builtExprMap = dict() # map expr-ids to "built" expressions (whatever exprBuilderFn returns)
        for exprId in reversed(exprIds):
            subExpressions =  [builtExprMap[subExprId] for subExprId in subExprIdsMap[exprId]]
            builtExprMap[exprId] = exprBuilderFn(exprClassStrs[exprId], coreInfoMap[exprId], subExpressions)
        return builtExprMap[masterExprId]        
    
    def clean(self):
        '''
        Clean the _pv_it_ directory by erasing anything with a reference
        count of zero.
        '''
        for sub_dir in os.listdir(self.pv_it_dir):
            if sub_dir == '_axioms_' or sub_dir == '_theorems_':
                continue
            sub_path = os.path.join(self.pv_it_dir, sub_dir)
            if os.path.isdir(sub_path):
                # assume this is a hash directory for a prove-it object if it isn't _axioms_ or _theorems_
                hash_directory = sub_dir 
                if self._getRefCount(hash_directory) == 0:
                    self._removeReference(hash_directory)
    
    """    
    # This is not good to do if there are external references
           
    def erase(self):
        '''
        Erase the entire _pv_it_ directory.
        '''
        self._proveItObjects.clear()
        pv_it_dir = os.path.join(self.directory, '_pv_it_')
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
            self.path = os.path.join(self.context._storage.directory, '_axioms_', self.name)
        elif kind == 'theorem':
            self.path = os.path.join(self.context._storage.directory, '_theorems_', self.name) 
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")

    def __str__(self):
        return self.context.name + '.' + self.name
    
    def remove(self, keepPath=False):
        '''
        Remove the axiom or theorem and all references to it and any proofs
        that depend upon it.
        '''
        from context import Context
        # remove the reference to the expression to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'expr.pv_it'), 'r') as f:
            expr_id = f.read()
            self.storage._removeReference(expr_id)
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
        with open(os.path.join(self.path, 'usedBy.txt'), 'r') as usedByFile:
            for line in usedByFile:
                theorems.append(line.strip())
        return theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the given 
        theorem or axiom directly or indirectly.
        '''
        from context import Context
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
        _pv_it_ database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'axiom')

class StoredTheorem(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredTheorem object for managing a theorem's
        _pv_it_ database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'theorem')

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
        usedAxioms = set()
        usedTheorems = set()
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            try:
                with open(os.path.join(self.path, usedStmtsFilename), 'r') as usedStmtsFile:
                    for line in usedStmtsFile:
                        line = line.strip()
                        usedStmts.add(line)
            except IOError:
                pass # no contribution if the file doesn't exist
        return (usedAxioms, usedTheorems)

    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  Updates
        dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
        and proven dependency indicators (various provenTheorems.txt files 
        for theorems that depend upon this one) appropriately.
        '''
        from proveit._core_ import Proof
        from context import Context
        
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()
                    
        # record the proof id
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        proofId = self.storage._proveItStorageId(proof)
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
            self.storage._addReference(proofId)
        
        usedAxioms = [str(usedAxiom) for usedAxiom in proof.usedAxioms()]
        usedTheorems = [str(usedTheorem) for usedTheorem in proof.usedTheorems()]
        
        # Remove usedBy links that are obsolete because the proof has changed
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for prevUsedAxiom in prevUsedAxioms:
            if prevUsedAxiom not in usedAxioms:
                Context.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(str(self))
        for prevUsedTheorem in prevUsedTheorems:
            if prevUsedTheorem not in usedTheorems:
                Context.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(str(self))
        
        # record axioms/theorems that this theorem directly uses
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for usedStmt in sorted(usedStmts):
                    self.context._includeMutualReferences(usedStmt.context)
                    usedStmtsFile.write(usedStmt + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheorems:
                if Context.getStoredTheorem(usedTheorem).isComplete():
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the newly proven theorem
        storedUsedAxioms = [axiom._storedAxiom() for axiom in usedAxioms]
        storedUsedTheorems = [theorem._storedTheorem() for theorem in usedTheorems]
        for storedUsedStmts, prevUsedStmts in ((storedUsedAxioms, prevUsedAxioms), (storedUsedTheorems, prevUsedTheorems)):
            for storedUsedStmt in storedUsedStmts:
                if str(storedUsedStmt) not in prevUsedStmts: # otherwise the link should already exist
                    with open(os.path.join(storedUsedStmt.path, 'usedBy.txt'), 'a') as usedByFile:
                        usedByFile.write(str(self) + '\n')
        
        print str(self) + ' has a proof'
        # if this proof is complete (all of the theorems that it uses are complete) then
        # propagate this information to the theorems that depend upon this one.
        self._propagateCompletion()
    
    def hasProof(self):
        '''
        Returns True iff a proof was recorded for this theorem.
        '''
        return os.path.isfile(os.path.join(self.path, 'proof.pv_it'))
    
    def numUsedTheorems(self):
        return self._countEntries('usedTheorems.txt')

    def numCompleteUsedTheorems(self):
        return self._countEntries('completeUsedTheorems.txt')
    
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
        from context import Context
        if self.isComplete():
            print str(self) + ' has been completely proven'
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
        from context import Context 
        wasComplete = self.isComplete() # was it complete before the proof was removed?
        # remove the reference to the proof to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'proof.pv_it'), 'r') as f:
            proof_id = f.read()
            self.storage._removeReference(proof_id)
        # Remove obsolete usedBy links that refer to this theorem by its old proof
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for usedAxiom in prevUsedAxioms:
            Context.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheorems:
            Context.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform dependents that
        # it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
        # remove 'proof.pv_it', 'usedAxioms.txt', 'usedTheorems.txt', and 'completeUsedTheorems.txt' for the theorem
        os.remove(os.path.join(self.path, 'proof.pv_it'))
        os.remove(os.path.join(self.path, 'usedAxioms.txt'))
        os.remove(os.path.join(self.path, 'usedTheorems.txt'))
        os.remove(os.path.join(self.path, 'completeUsedTheorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        from context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        usedAxioms, usedTheorems = self.readDependencies()
        requiredAxioms = usedAxioms # just a start
        requiredTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                requiredTheorems.add(nextTheorem)
                processed.add(nextTheorem)
                continue
            usedAxioms, usedTheorems = storedTheorem.readDependencies()
            requiredAxioms.update(usedAxioms)
            for usedTheorem in usedTheorems:
                if usedTheorem not in processed:
                    toProcess.add(usedTheorem)
            processed.add(nextTheorem)
        return (requiredAxioms, requiredTheorems)
    
    def allUsedTheorems(self):
        '''
        Returns the set of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        from context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        _, usedTheorems = self.readDependencies()
        allUsedTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            allUsedTheorems.add(nextTheorem)
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                processed.add(nextTheorem)
                continue
            _, usedTheorems = storedTheorem.readDependencies()
            for usedTheorem in usedTheorems:
                if usedTheorem not in processed:
                    toProcess.add(usedTheorem)
            processed.add(nextTheorem)
        return allUsedTheorems 

    def _undoDependentCompletion(self, usedTheorem):
        '''
        Due to the proof being removed, a dependent theorem is no longer complete.
        This new status must be updated and propagated.
        '''
        from context import Context
        wasComplete = self.isComplete() # was it complete before?
        # remove the entry from completeUsedTheorems.txt
        self._removeEntryFromFile('completeUsedTheorems.txt', str(usedTheorem))
        if self.isComplete():
            raise Exception('Corrupt _certified_ database')
        # If this theorem was previously complete before, we need to inform 
        # dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
