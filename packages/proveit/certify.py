"""
certify.py acts as the gatekeeper to the '_certified_' database.
The '_certified_' database stores, for any given Prove-It
package, sets of axioms, theorems, and proofs associated 
with theorems.  Proof dependencies are checked to ensure
that the logic is not circular.

A theorem may have only one proof associated with it
at any time (proofs may be replaced).  If one wishes
to have multiple proofs associated with a particular
theorem (e.g., for pedagogical reasons), the way to
do this is to create multiple theorems (multiple names)
for the same expression.  That way, the dependencies
between theorem, which is important to track in
order to prevent circular logic, will be unambiguous
(not confused with multiple proofs per theorem).
"""

from proveit._core_.storage import Storage
import os, shutil
import proveit

def _makeStorage(package):
    return Storage(os.path.join(*([proveit.__path__[0]] + ['..', '_certified_'] + package.split('.'))), refCounted=True)

class _StoredSpecialStmt:
    def __init__(self, stmtStr, stmtType):
        segments = stmtStr.split('.')
        self.package = '.'.join(segments[0:-1])
        self.name = segments[-1]
        self.stmtType = stmtType
        self.storage = _makeStorage(self.package)
        if stmtType == 'axiom':
            self.path = os.path.join(self.storage.directory, '_axioms_', self.name)
        elif stmtType == 'theorem':
            self.path = os.path.join(self.storage.directory, '_theorems_', self.name)        

    def __str__(self):
        return self.package + '.' + self.name
    
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
            _StoredTheorem(dependent).removeProof()
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
    
class _StoredAxiom(_StoredSpecialStmt):
    def __init__(self, axiom):
        '''
        Creates a _StoredAxiom object that refers to the _certified_ database
        storage of the given axiom (as a string or an Prove-It Axiom object
        that can be converted to a string that expresses the package and name
        of the axiom).
        '''
        from proveit import KnownTruth, Axiom
        if isinstance(axiom, KnownTruth):
            # attempt to get an Axiom object from the KnownTruth
            axiom = axiom.asTheoremOrAxiom()
            if not isinstance(axiom, Axiom):
                raise ValueError('Expecting an Axiom not a Theorem')
        _StoredSpecialStmt.__init__(self, str(axiom), 'axiom')

class _StoredTheorem(_StoredSpecialStmt):
    def __init__(self, theorem):
        '''
        Creates a _StoredTheorem object that refers to the _certified_ database
        storage of the given theorem (as a string or an Prove-It Theorem object
        that can be converted to a string that expresses the package and name
        of the axiom).
        '''
        from proveit import KnownTruth, Theorem
        if isinstance(theorem, KnownTruth):
            # attempt to get an Axiom object from the KnownTruth
            theorem = theorem.asTheoremOrAxiom()
            if not isinstance(theorem, Theorem):
                raise ValueError('Expecting an Theorem not a Axiom')
        _StoredSpecialStmt.__init__(self, str(theorem), 'theorem')

    def remove(self, keepPath=False):
        if self.hasProof():
            # must remove the proof first
            self.removeProof()
        _StoredSpecialStmt.remove(self, keepPath)

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
                _StoredAxiom(prevUsedAxiom)._removeUsedByEntry(str(self))
        for prevUsedTheorem in prevUsedTheorems:
            if prevUsedTheorem not in usedTheorems:
                _StoredTheorem(prevUsedTheorem)._removeUsedByEntry(str(self))
        
        # record axioms/theorems that this theorem directly uses
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for usedStmt in sorted(usedStmts):
                    usedStmtsFile.write(usedStmt + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheorems:
                if isFullyProven(usedTheorem):
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the newly proven theorem
        storedUsedAxioms = [_StoredAxiom(axiom) for axiom in usedAxioms]
        storedUsedTheorems = [_StoredTheorem(theorem) for theorem in usedTheorems]
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
                storedDependent = _StoredTheorem(dependent)
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
            _StoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheorems:
            _StoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform dependents that
        # it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                _StoredTheorem(dependent)._undoDependentCompletion(str(self))
        # remove 'proof.pv_it', 'usedAxioms.txt', 'usedTheorems.txt', and 'completeUsedTheorems.txt' for the theorem
        os.remove(os.path.join(self.path, 'proof.pv_it'))
        os.remove(os.path.join(self.path, 'usedAxioms.txt'))
        os.remove(os.path.join(self.path, 'usedTheorems.txt'))
        os.remove(os.path.join(self.path, 'completeUsedTheorems.txt'))

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
                _StoredTheorem(dependent)._undoDependentCompletion(str(self))
        
def exportCertificates(packages):
    pass

def importCertificates(certificates):
    pass

def _makeStoredSpecialStmt(theoremOrAxiom, kind=None):
    from proveit import Axiom, Theorem, KnownTruth 
    if isinstance(theoremOrAxiom, KnownTruth):
        # attempt to get a Theorem or Axiom object from the KnownTruth
        theoremOrAxiom = theoremOrAxiom.asTheoremOrAxiom()
    if kind == 'axiom':
        return _StoredAxiom(theoremOrAxiom)
    elif kind == 'theorem':
        return _StoredTheorem(theoremOrAxiom)
    elif isinstance(theoremOrAxiom, Axiom):
        return _StoredAxiom(theoremOrAxiom)
    elif isinstance(theoremOrAxiom, Theorem):
        return _StoredTheorem(theoremOrAxiom)
    else:
        raise TypeError("theoremOrAxiom should be a string, Axiom, Theorem, or KnownTruth with a Theorem/Axiom proof")

def _setSpecialStatements(package, kind, definitions):
    storage = _makeStorage(package)
    specialStatementsPath = os.path.join(storage.directory, '_' + kind + '_')
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
            raise Exception('corrupted _certified_ directory')
    # Remove the special statements that no longer exist
    for name in toRemove:
        print 'Removing ' + kind + ': ' + package + '.' + name + ' from _certified_ database'
        _makeStoredSpecialStmt(package + '.' + name, kind[:-1]).remove()
        
    # Update the definitions
    for name, expr in definitions.iteritems():
        # add the expression to the "database" via the storage object.
        exprId = storage._proveItObjId(expr)
        if name in previousDefIds and previousDefIds[name] == exprId:
            continue # unchanged special statement
        storedSpecialStmt = _makeStoredSpecialStmt(package + '.' + name, kind[:-1])
        if name not in previousDefIds:
            # added special statement
            print 'Adding new ' + kind + ' to _certified_ database: ' + package + '.' + name 
        elif previousDefIds[name] != exprId:
            # modified special statement. remove the old one first.
            print 'Modifying ' + kind + ' in _certified_ database: ' + package + '.' + name 
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
            
def _getSpecialStatement(package, kind, name):
    storage = _makeStorage(package)
    specialStatementsPath = os.path.join(storage.directory, '_' + kind + '_')
    try:
        with open(os.path.join(specialStatementsPath, name, 'expr.pv_it'), 'r') as f:
            exprId = f.read()
            return storage.makeExpression(exprId)
    except IOError:
        raise Exception('corrupted _certified_ directory')


def setAxioms(package, axioms):
    _setSpecialStatements(package, 'axioms', axioms)

def setTheorems(package, theorems):
    _setSpecialStatements(package, 'theorems', theorems)

def getAxiom(package, name):
    from proveit import Axiom
    return Axiom(_getSpecialStatement(package, 'axioms', name), package, name).provenTruth
    
def getTheorem(package, name):
    from proveit import Theorem
    return Theorem(_getSpecialStatement(package, 'theorems', name), package, name).provenTruth
    
def recordProof(theorem, proof):
    '''
    Record the given proof as the proof of the theorem.  Updates
    dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
    and proven dependency indicators (various provenTheorems.txt files 
    for theorems that depend upon the one being proven) appropriately.
    '''
    _StoredTheorem(theorem).recordProof(proof)

def removeProof(theorem):
    '''
    Remove the proof for the given theorem and all obsolete dependency
    links.
    '''
    _StoredTheorem(theorem).removeProof()
    
def hasProof(theorem):
    return _StoredTheorem(theorem).hasProof()

def isFullyProven(theorem):
    return _StoredTheorem(theorem).isComplete()

def allRequirements(theorem):
    '''
    Returns the set of axioms that are required (directly or indirectly)
    by the theorem.  Also, if the given theorem is not completely proven,
    return the set of unproven theorems that are required (directly or
    indirectly).  Returns this axiom set and theorem set as a tuple.
    '''
    if not hasProof(theorem):
        raise Exception('The theorem must be proven in order to obtain its requirements')
    storedTheorem = _StoredTheorem(theorem)
    usedAxioms, usedTheorems = storedTheorem.readDependencies()
    requiredAxioms = usedAxioms # just a start
    requiredTheorems = set()
    processed = set()
    toProcess = usedTheorems
    while len(toProcess) > 0:
        nextTheorem = toProcess.pop()
        storedTheorem = _StoredTheorem(nextTheorem)
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

def allUsedTheorems(theorem):
    '''
    Returns the set of theorems used to prove the given theorem, directly
    or indirectly.
    '''
    if not hasProof(theorem):
        raise Exception('The theorem must be proven in order to obtain its requirements')
    storedTheorem = _StoredTheorem(theorem)
    _, usedTheorems = storedTheorem.readDependencies()
    allUsedTheorems = set()
    processed = set()
    toProcess = usedTheorems
    while len(toProcess) > 0:
        nextTheorem = toProcess.pop()
        allUsedTheorems.add(nextTheorem)
        storedTheorem = _StoredTheorem(nextTheorem)
        if not storedTheorem.hasProof():
            processed.add(nextTheorem)
            continue
        _, usedTheorems = storedTheorem.readDependencies()
        for usedTheorem in usedTheorems:
            if usedTheorem not in processed:
                toProcess.add(usedTheorem)
        processed.add(nextTheorem)
    return allUsedTheorems 

def allDependents(theoremOrAxiom, kind=None):
    '''
    Returns the set of theorems that are known to depend upon the given 
    theorem or axiom directly or indirectly.  kind must be 'axiom' or 'theorem'
    if theoremOrAxiom is in the form of a string (or it should be an Axiom
    or Theorem object).
    '''
    storedStmt = _makeStoredSpecialStmt(theoremOrAxiom, kind)
    toProcess = set(storedStmt.readDependentTheorems())
    processed = set()
    while len(toProcess) > 0:
        nextTheorem = toProcess.pop()
        processed.add(nextTheorem)
        storedTheorem = _StoredTheorem(nextTheorem)
        dependents = set(storedTheorem.readDependentTheorems())
        # add anything new to be processed
        toProcess.update(dependents.difference(processed))
    return processed
