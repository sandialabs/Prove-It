import hashlib, os
import shutil

class Storage:
    '''
    Manages the _pv_it_ directory of a Context, the distributed database
    of expressions, axioms, theorems, and proofs.
    '''
    
    def __init__(self, context, directory):
        self.context = context
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '_pv_it_')
        if not os.path.isdir(self.pv_it_dir):
            # make the directory for the storage
            os.makedirs(self.pv_it_dir)
        
        if self.context.isRoot():
            # map context names to paths for other known root contexts
            self.rootContextPaths = dict()
            self.paths_filename = os.path.join(self.pv_it_dir, 'paths.txt')
            if os.path.isfile(self.paths_filename):
                with open(self.paths_filename) as paths_file:
                    for path_line in paths_file.readlines():
                        context_name, path = path_line.split()
                        if context_name == '.' and path != directory:
                            # the directory of the context associated with this storage object has changed.
                            self.update_path()
                        else:
                            self.rootContextPaths[context_name] = path
            else:
                with open(self.paths_filename, 'w') as paths_file:
                    # the first entry indicates the directory of this path
                    paths_file.write('. ' + directory + '\n')
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    
    def update_path(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Context's.
        '''
        pass
        
    def includeReferences(self, otherStorage):
        '''
        Include a path reference from a root Context to another root Context,
        both in the rootContextPaths dictionary and in the paths.txt file. 
        '''
        from Context import ContextException
        otherContextName = otherStorage.context.name
        if otherContextName not in self.rootContextPaths:
            self.rootContextPaths[otherContextName] = otherStorage.directory
            with open(self.paths_filename, 'w') as paths_file:
                paths_file.write(otherContextName + ' ' + otherStorage.directory + '\n')
        elif self.context_path[otherContextName] != otherStorage.directory:
            raise ContextException(self.context, "Conflicted directory references to context '%s'"%otherContextName)
    
    def getContext(self, contextName):
        '''
        Return the Context with the given name according to known paths of Context
        roots.
        '''
        from context import Context, ContextException
        splitContextName = contextName.split('.')
        otherRoot = splitContextName[0]
        if otherRoot == self.context.rootContext.name:
            # Context with the same root as this one
            return Context(os.path.join(*([self.directory]+splitContextName[1:])))
        else:
            # Context with a different root than this one; need to get the path of the other root.
            if otherRoot not in self.rootContextPaths:
                raise ContextException(self.context, "Context root '%s' is unknown"%otherRoot)
            otherRootDirectory = self.rootContextPaths[otherRoot]
            return Context(os.path.join(*([otherRootDirectory]+splitContextName[1:])))
    
    def retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Find the .png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and path where the png is stored as a tuple.
        '''
        pv_it_filename = self._retrieve(expr)
        # generate the latex and png file paths, from pv_it_filename and the distinction 
        latex_path = os.path.join(self.pv_it_dir, pv_it_filename[:-6] + '.latex')
        png_path = os.path.join(self.pv_it_dir, pv_it_filename[:-6] + '.png')
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
       
    def _proveItObjId(self, proveItObjectOrFilename):
        '''
        Retrieve a unique id for the Prove-It object based upon its pv_it filename from calling _retrieve.
        '''
        if isinstance(proveItObjectOrFilename, str):
            pv_it_filename = proveItObjectOrFilename
        else:
            pv_it_filename = self._retrieve(proveItObjectOrFilename)
        # (replace os.path.sep within pv_it file paths with '/' to make this OS neutral just in case)
        return '/'.join(pv_it_filename.split(os.path.sep))
    
    
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
        return prefix + proveItObject._generate_unique_rep(self._proveItObjId)
    
    def _extractReferencedObjIds(self, unique_rep):
        '''
        Given a unique representation string, returns the list of Prove-It objects
        that are referenced.
        '''
        from proveit import Expression, KnownTruth, Proof
        if unique_rep[:6] == 'Proof:':
            return Proof._extractReferencedObjIds(unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            return KnownTruth._extractReferencedObjIds(unique_rep[11:])
        else:
            # Assumed to be an expression then
            return Expression._extractReferencedObjIds(unique_rep)

    def _addReference(self, proveItObjId):
        '''
        Increment the reference count of the prove-it object with the given
        storage identifier.  The .pv_it file is  updated with the new 
        reference count.
        '''
        # replace '/' with os.path.sep within the Prove-It object id to object the filename
        pv_it_filename = os.path.sep.join(proveItObjId.split('/'))
        pv_it_dir = self.pv_it_dir
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            refCount = int(refCount)
            refCount += 1
            # change the reference count in the file
            with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f2:
                f2.write(str(refCount)+'\n')
                f2.write(str(rep))

    def _getRefCount(self, proveItObjId):
        '''
        Return the reference coult of the prove-it object with the given
        storage identifier.
        '''
        pv_it_filename = os.path.sep.join(proveItObjId.split('/'))
        pv_it_dir = self.pv_it_dir
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            return refCount
                                                
    def _removeReference(self, proveItObjId):
        '''
        Decrement the reference count of the prove-it object with the given
        storage identifier.  If the reference count goes down to zero, then
        the files storing this prove-it object's data will be deleted
        (and the directory if nothing else is in it).  Otherwise, the
        .pv_it file is simply updated with the new reference count.
        '''
        # replace '/' with os.path.sep within the Prove-It object id to object the filename
        pv_it_filename = os.path.sep.join(proveItObjId.split('/'))
        pv_it_dir = self.pv_it_dir
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            refCount = int(refCount)
            refCount -= 1
        if refCount <= 0:
            # Reference count down to zero (or less).  Remove references to
            # referenced objects and then delete this prove-it object
            # and everything associated with it.
            for objId in self._extractReferencedObjIds(rep):
                self._removeReference(objId)
            # remove all files associated with this prove-it object 
            # and perhaps the entire directory.
            relpath, filename = os.path.split(pv_it_filename)
            fileroot = filename[:-6]
            for filename in os.listdir(os.path.join(pv_it_dir, relpath)):
                if filename[:len(fileroot)] == fileroot:
                    os.remove(os.path.join(pv_it_dir, relpath, filename))
            if len(os.listdir(os.path.join(pv_it_dir, relpath))) == 0:
                # the directory is now empty.  remove it.
                os.rmdir(os.path.join(pv_it_dir, relpath))
        else:
            # change the reference count in the file
            with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f:
                f.write(str(refCount)+'\n')
                f.write(str(rep))

    
    def _retrieve(self, proveItObject):
        '''
        Find the .pv_it file for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the .pv_it filename, relative to
        the .pv_it directory.
        '''
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        pv_it_dir = self.pv_it_dir
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        if not os.path.exists(pv_it_dir):
            os.mkdir(pv_it_dir)
        hash_path = os.path.join(pv_it_dir, rep_hash)
        if not os.path.exists(hash_path):
            os.mkdir(hash_path)
        # check for existing files in this hash value sub-directory to see if the right one is there
        for expr_file in os.listdir(hash_path):
            if expr_file[-6:] == '.pv_it':
                pv_it_filename = os.path.join(rep_hash, expr_file)
                with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
                    contents = f.read()
                    refCount, rep = contents.split('\n') 
                    if rep == unique_rep:
                        # an existing file contains the exported expression
                        self._pv_it_filename = pv_it_filename
                        # remember this for next time
                        self._proveItObjects[proveItObject] = pv_it_filename
                        return pv_it_filename
        # does not exist, create a new file (checking against an unlikely collision)
        index = 0
        while os.path.exists(os.path.join(hash_path, str(index) + '.pv_it')):
            index += 1
        pv_it_filename = os.path.join(rep_hash, str(index) + '.pv_it')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f:
            # first write a reference count of 0 (until a reference is added)
            f.write(str(0) + '\n')
            f.write(unique_rep) # write the unique representation to a file
        # increment reference counts of the referenced objects
        for objId in self._extractReferencedObjIds(unique_rep):
            self._addReference(objId)
        # remember this for next time
        self._proveItObjects[proveItObject] = pv_it_filename
        return pv_it_filename
    
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
        # (replace '/' within exprId with os.path.sep to convert it to a file name
        # regardless of OS).
        from proveit import Expression
        from _dependency_graph import orderedDependencyNodes
        pv_it_dir = self.pv_it_dir
        exprClassStrs = dict() # map expr-ids to Expression class string representations
        coreInfoMap = dict() # map expr-ids to core information
        subExprIdsMap = dict() # map expr-ids to list of sub-expression ids 
        masterExprId = exprId
        def getSubExprIds(exprId):
            pv_it_filename = os.path.sep.join(exprId.split('/'))
            with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
                # extract the unique representation from the pv_it file
                contents = f.read()
                refCount, unique_rep = contents.split('\n') 
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
            if sub_dir == '_axioms_' or sub_dir == '_theorems_' or sub_dir == '_common_':
                continue
            pv_it_dir = os.join(self.pv_it_dir, sub_dir)
            if os.isdir(pv_it_dir):
                for pv_it_filename in os.listdir(pv_it_dir):
                    if not os.isfile(pv_it_filename) or pv_it_filename[-6:] != '.pv_it':
                        continue
                    objId = self._proveItObjId(pv_it_filename)
                    if self._getRefCount(objId) == 0:
                        self._removeReference(objId)
                        
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
    
class StoredSpecialStmt:
    def __init__(self, context, kind, name):
        '''
        Base class of StoredAxiom and StoredTheorem initialization.
        '''
        self.context = context
        self.name = name
        self.kind = kind
        if kind == 'axiom':
            self.path = os.path.join(self.storage.directory, '_axioms_', self.name)
        elif kind == 'theorem':
            self.path = os.path.join(self.storage.directory, '_theorems_', self.name) 
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")

    def __str__(self):
        return self.context.name + '.' + self.name
    
    def remove(self, keepPath=False):
        '''
        Remove the axiom or theorem and all references to it and any proofs
        that depend upon it.
        '''
        # remove the reference to the expression to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'expr.pv_it'), 'r') as f:
            expr_id = f.read()
            self.storage._removeReference(expr_id)
        # remove invalidated proofs that use this axiom/theorem
        dependentTheorems = self.readDependentTheorems()
        for dependent in dependentTheorems:
            self.context.getStoredTheorem(dependent).removeProof()
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
        toProcess = set(self.readDependentTheorems())
        processed = set()
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            processed.add(nextTheorem)
            storedTheorem = self.context.getStoredTheorem(nextTheorem)
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
        
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()
            
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        proofId = self.storage._proveItObjId(proof)
        # also store the png 
        self.storage._retrieve_png(proof, proof.latex(), proof._config_latex_tool)
        
        # record the proof id
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
            self.storage._addReference(proofId)
        
        usedAxioms = [str(usedAxiom) for usedAxiom in proof.usedAxioms()]
        usedTheorems = [str(usedTheorem) for usedTheorem in proof.usedTheorems()]
        
        # Remove usedBy links that are obsolete because the proof has changed
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for prevUsedAxiom in prevUsedAxioms:
            if prevUsedAxiom not in usedAxioms:
                self.context.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(str(self))
        for prevUsedTheorem in prevUsedTheorems:
            if prevUsedTheorem not in usedTheorems:
                self.context.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(str(self))
        
        # record axioms/theorems that this theorem directly uses
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for usedStmt in sorted(usedStmts):
                    self.context._includeMutualReferences(usedStmt.context)
                    usedStmtsFile.write(usedStmt + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheorems:
                if self.context.getStoredTheorem(usedTheorem).isComplete():
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
        if self.isComplete():
            print str(self) + ' has been completely proven'
            # This theorem has been completely proven.  Let the dependents know.
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                storedDependent = self.context.getStoredTheorem(dependent)
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
        wasComplete = self.isComplete() # was it complete before the proof was removed?
        # remove the reference to the proof to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'proof.pv_it'), 'r') as f:
            proof_id = f.read()
            self.storage._removeReference(proof_id)
        # Remove obsolete usedBy links that refer to this theorem by its old proof
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for usedAxiom in prevUsedAxioms:
            self.context.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheorems:
            self.context.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform dependents that
        # it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                self.context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
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
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        usedAxioms, usedTheorems = self.readDependencies()
        requiredAxioms = usedAxioms # just a start
        requiredTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            storedTheorem = self.getStoredTheorem(nextTheorem)
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
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        _, usedTheorems = self.readDependencies()
        allUsedTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            allUsedTheorems.add(nextTheorem)
            storedTheorem = self.context.getStoredTheorem(nextTheorem)
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
                self.context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
