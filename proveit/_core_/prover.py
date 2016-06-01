from proveit._core_.statement import Statement, asStatement

class Prover:
    # Temporary provers: mapping a statement to a list of provers (for various assumption sets).
    # After proving a theorem via the qed method, the temporary provers will be cleared.
    _tmpProvers = dict()
    
    def __init__(self, stmtToProve, assumptions, impliedParent=None, proverType="root", newAssumptionsInOrder=None):
        # if this is proven, along with any corequisites, the impliedParent is also proven
        assert impliedParent != self
        self.impliedParent = impliedParent 
        self.stmtToProve = stmtToProve
        self.assumptions = frozenset(assumptions)
        self.proverType = proverType
        self.subMap = None # set for specialization provers (substitution map)
        self.relabelMap = None # set for specialization provers (relabeling map)
        if impliedParent == None:
            self.depth = 0
        else:
            self.depth = impliedParent.depth+1
        self.corequisites = [self]
        self.provers = None # when proven, what Prover's provide the proof for this one
        # subset of the assumptions which proves self.stmtToProve
        self.provingAssumptions = None
        if self.stmtToProve.isAxiom():
            self.provingAssumptions = frozenset()
        elif self.stmtToProve.wasProven(assumptions):
            self.provingAssumptions = self.stmtToProve.provingAssumptions(assumptions)
            self.provers = self.stmtToProve.getProver(assumptions).provers
        elif stmtToProve in assumptions:
            self.provingAssumptions = frozenset([stmtToProve])
#            # see whether or not it was already proven for a subset of the assumptions
#            if self.stmtToProve.provingStatements(self.provingAssumptions) == None:
#                self.provingAssumptions = None
        # For keeping the order of the new assumptions
        if newAssumptionsInOrder is None:
            self.newAssumptionsInOrder = tuple()
        else:
            self.newAssumptionsInOrder = tuple(newAssumptionsInOrder) 
    
    def _export_pvit(self, path, pvit_file, expressions_dir, indentation = ''):
        '''
        Export the proof information to .pv_it files for the purpose of proof
        certification.  This occurs behind-the-scenes when the qed() method of
        an expression is called (and is therefore not a "public" method).
        '''
        import os
        expr_id = self.stmtToProve.getExpression()._export_pvit(expressions_dir)
        pvit_file.write(indentation + self.proverType + ' ' + expr_id)
        if self.proverType == 'specializing':
            pvit_file.write(' via')
            if self.subMap is not None and len(self.subMap) > 0:
                pvit_file.write(' substituting ' + str({key._export_pvit(expressions_dir):val._export_pvit(expressions_dir) for key, val in self.subMap}))
            if self.relabelMap is not None and len(self.relabelMap) > 0:
                pvit_file.write(' relabeling ' + str({key._export_pvit(expressions_dir):val._export_pvit(expressions_dir) for key, val in self.relabelMap}))
        if self.provingAssumptions is not None and len(self.provingAssumptions) > 0:
            assumption_ids = [assumption.getExpression()._export_pvit(expressions_dir) for assumption in self.provingAssumptions]
            pvit_file.write(' assuming ' + ', '.join(assumption_ids))
        pvit_file.write('\n')
        indentation += '\t'
        if self.stmtToProve.isAxiom():
            pvit_file.write(indentation + 'by axiom ' + self.stmtToProve._package + '.' + self.stmtToProve._name + '\n')
        elif self.stmtToProve.isNamedTheorem():
            pvit_file.write(indentation + 'by theorem ' + self.stmtToProve._package + '.' + self.stmtToProve._name + '\n')
        elif self.proverType != 'root' and self.stmtToProve.isProvenTheorem():
            pvit_file.write(indentation + 'by unnamed theorem\n')
            # export the unnamed theorem
            expr_sub_dirs = expr_id.split('/')
            unnamed_proof_dir = os.path.join(path, '__unnamed__', expr_sub_dirs[0])
            if not os.path.exists(unnamed_proof_dir):
                os.makedirs(unnamed_proof_dir)
            with open(os.path.join(unnamed_proof_dir, expr_sub_dirs[1] + '.pv_it'), 'w') as unnamed_theorem_proof_file:
                storeType = self.proverType
                self.proverType = 'root'
                self._export_pvit(path, unnamed_theorem_proof_file, expressions_dir)
                self.proverType = storeType
        elif self.provers is not None:
            for prover in self.provers:
                prover._export_pvit(path, pvit_file, expressions_dir, indentation)

    def statementAndAssumptions(self):
        '''
        Return the statement and assumptions for the prover in a hashable form.
        '''
        return (self.stmtToProve, tuple([assumption for assumption in self.provingAssumptions]))

    def showProof(self):
        visitedStmtAndAsumptions = set()
        nextProvers = [self]
        enumeratedProvers = []
        while len(nextProvers) > 0:
            nextProver = nextProvers.pop(0)
            stmtAndAssumptions = nextProver.statementAndAssumptions()
            if stmtAndAssumptions in visitedStmtAndAsumptions: continue # already showed that one
            visitedStmtAndAsumptions.add(stmtAndAssumptions)
            enumeratedProvers.append(nextProver)
            if nextProver.provers is not None:
                nextProvers += nextProver.provers
        proverNumMap = {prover.statementAndAssumptions():k for k, prover in enumerate(enumeratedProvers)}
        print r'\begin{tabular}{rl|l|l|l}'
        print r' & \textbf{statement} & \textbf{assumptions} & \textbf{step type} & \textbf{requirements} \\'
        for k, prover in enumerate(enumeratedProvers):
            print r'\hline'
            if prover.provers is None:
                requirements = []
                stepType = ''
            else:
                requirements = prover.provers
                if requirements[0].proverType == 'generalizing':
                    stepType = 'generalization'
                elif requirements[0].proverType == 'specializing':
                    stepType = r'$\begin{array}{l} '
                    if requirements[0].subMap is not None and len(requirements[0].subMap) > 0:
                        stepType += r'{\rm specialization~via} \\ '
                        stepType += r'\left\{' + ',~'.join(key.latex() + ': ' + val.latex() for key, val in requirements[0].subMap) + r'\right\}'
                    if requirements[0] is not None and len(requirements[0].relabelMap) > 0:
                        stepType += r'{\rm relabeling via} \\ '
                        stepType += r'\left\{' + ',~'.join(key.latex() + ': ' + val.latex() for key, val in requirements[0].relabelMap) + r'\right\}'
                    stepType += r'\end{array}$'
                elif requirements[0].proverType == 'implication':
                    stepType = 'modus ponens'
                elif requirements[0].proverType == 'hypothetically reasoning':
                    stepType = 'hypothetical reasoning'
            print str(k) + '. & ' + repr(prover.stmtToProve.getExpression()) + ' & ',
            if prover.stmtToProve.isAxiom() or prover.stmtToProve.isNamedTheorem():
                print r'\multicolumn{3}{|l}{',
                if prover.stmtToProve.isAxiom():
                    print r'axiom: ',
                elif prover.stmtToProve.isNamedTheorem():
                    print r'theorem: ',
                print prover.stmtToProve._package + '.' + prover.stmtToProve._name + r'} \\'
            else:
                print ', '.join(repr(assumption.getExpression()) for assumption in prover.provingAssumptions) \
                    + ' & ' + stepType + ' & ' + ', '.join([str(proverNumMap[requirement.statementAndAssumptions()]) for requirement in requirements]) + r' \\'
        print r'\hline'
        print r'\end{tabular}'
        
    """    
    def showProof(self, indentation='', remembered = None, usedAxioms = None, usedTheorems = None):
        if remembered is None: 
            remembered = set()
            usedAxioms = set()
            usedTheorems = set()
        numNodes = 1
        print (indentation + r'\item ' + self.proverType + ' ' + repr(self.stmtToProve.getExpression())),
        if self.provingAssumptions is not None and len(self.provingAssumptions) > 0:
            print ' assuming', ', '.join(repr(assumption.getExpression()) for assumption in self.provingAssumptions),
        key = (self.stmtToProve,) + tuple([assumption for assumption in self.provingAssumptions])
        if key in remembered:
            print ' proven above'
            return 0 # don't count this as a separate node
        if len(indentation) > 0:
            remembered.add(key) # don't add the top-level theorem
        '''
        if self.proverType == 'specializing':
            print ' via',
            if self.subMap is not None and len(self.subMap) > 0:
                print ' substituting', str({key:val for key, val in self.subMap}),
            if self.relabelMap is not None and len(self.relabelMap) > 0:
                print ' relabeling', str({key:val for key, val in self.relabelMap}),
        '''
        print '' # new line
        indentation += '  '
        if self.stmtToProve.isAxiom():
            print r'\\'
            print indentation + r'by axiom \verb|' + self.stmtToProve._package + '.' + self.stmtToProve._name + '|'
            usedAxioms.add(self.stmtToProve._package + '.' + self.stmtToProve._name)
        elif self.stmtToProve.isNamedTheorem():
            print r'\\'
            print indentation + r'by theorem \verb|' + self.stmtToProve._package + '.' + self.stmtToProve._name + '|'
            usedTheorems.add(self.stmtToProve._package + '.' + self.stmtToProve._name)
        #elif self.proverType != 'root' and self.stmtToProve.isProvenTheorem():
        #    print indentation + 'by unnamed theorem'
        elif self.provers is not None:
            print r'\begin{itemize}'
            for prover in self.provers:
                numNodes += prover.showProof(indentation, remembered, usedAxioms, usedTheorems)  
            print r'\end{itemize}'
        if indentation == '  ':
            for axiom in sorted(usedAxioms):
                print axiom
            for thm in sorted(usedTheorems):
                print thm
            print "Number of used axioms:", len(usedAxioms)
            print "Number of used theorms:", len(usedTheorems)
            print "Number of derivation tree nodes:", numNodes      
        return numNodes
    """
    
    def isCircular(self, assumptions=None):
        '''
        Make sure we aren't stuck in circular logic.  Returns True if this derivation
        step is trying to prove itself up the chain under the given assumptions
        (default uses the assumptions of this Prover).
        '''
        if assumptions == None:
            assumptions = self.assumptions
        prover = self.impliedParent
        while prover != None:
            if prover.stmtToProve == self.stmtToProve and assumptions.issubset(prover.assumptions):
                return True # can't prove a statement via itself and no additional assumptions
            prover = prover.impliedParent
        return False
    
    def requirementsSatisfied(self):
        '''
        Is stmtToProve and any corequisite satisfied such that impliedParent is implied?
        '''
        return all([corequisite.wasProven() for corequisite in self.corequisites])
    
    def satisfyingAssumptions(self):
        provingAssumptionSets = [corequisite.provingAssumptions for corequisite in self.corequisites]
        return frozenset().union(*provingAssumptionSets)
    
    def completesProof(self):
        '''
        Go up the tree of impliedParents as long as requirements are satisfied, returning True
        if we get to the root.  While going up, records the first Provers to prove a Prover.
        '''
        prover = self
        while prover.requirementsSatisfied():
            #print prover, prover.depth
            satAssumptions = prover.satisfyingAssumptions()
#                provingStatements = frozenset({pvr.stmtToProve for pvr in prover.corequisites})
            provers = prover.corequisites
            prover = prover.impliedParent
            if prover == None:
                return True # main statement is proven
            prover.provers = provers
            # note that hypothetical reasoning and generalization condition 
            # assumptions get eliminated as we move up
            satAssumptions &= prover.assumptions
            prover.provingAssumptions = satAssumptions # proven by child(ren)
#                prover.stmtToProve._markAsProven(satAssumptions, prover)
            # remember that it is proven for this set of assumptions
#                #prover.stmtToProve.proofStepInfo.markAsProven(provingStatements, satAssumptions)
        return False
    
    def redundant(self):
        '''
        If any ancestor was already proven, this is redundant.
        '''
        prover = self
        if prover.wasProven(): return True
        while prover.impliedParent is not None:
            prover = prover.impliedParent
            if prover.wasProven(): return True
        return False

    def wasProven(self):
        return self.provingAssumptions is not None 
        
    def appendProvers(self, breadth1stQueue):
        '''
        Append any provers that can implicate that self is proven.
        '''
        from proveit import InSet
        stmt = self.stmtToProve
        # Prove by specialization?  Put this at front to connect with a theorem first if possible,
        for original, substitutionMap, relabelMap, conditions in stmt._specializers:
            generalityProver = Prover(original, self.assumptions - set(conditions), self, "specializing")
            generalityProver.subMap = substitutionMap
            generalityProver.relabelMap = relabelMap
            corequisites = [generalityProver] + [Prover(condition, self.assumptions, self, "condition") for condition in conditions]
            for prover in corequisites:
                prover.corequisites = corequisites
            #print [corequisite.stmtToProve.getExpression() for corequisite in corequisites]
            breadth1stQueue += corequisites
        # Prove by generalization?
        for original, forallVars, domain, conditions in stmt._generalizers:
            if domain is not None:
                conditions = [asStatement(InSet(var, domain)) for var in forallVars] + list(conditions)
            # we cannot allow assumptions that have any of the forallVars as free variables
            subAssumptions = {assumption for assumption in self.assumptions if len(assumption.freeVars() & set(forallVars)) == 0}            
            # add assumptions for any of the conditions of the generalizer
            subAssumptions |= set(conditions)
            breadth1stQueue.append(Prover(original, subAssumptions, self, "generalizing", newAssumptionsInOrder=conditions))
        # Truth by implication?
        for (hypothesis, implication) in stmt._implicators:
            # both hypothesis and implication must be proven for this to be sufficient, so they are cross requirements
            implicationProver = Prover(implication, self.assumptions, self, "implication")
            hypothesisProver = Prover(hypothesis, self.assumptions, self, "hypothesis")
            implicationProver.corequisites = hypothesisProver.corequisites = [implicationProver, hypothesisProver]
            breadth1stQueue += (implicationProver, hypothesisProver)
        # Prove by hypothetical reasoning?
        if stmt._hypothesisOfImplication != None:
            hypothesis = stmt._hypothesisOfImplication
            breadth1stQueue.append(Prover(stmt._conclusionOfImplication, self.assumptions | {hypothesis}, self, "hypothetically reasoning"))

    @staticmethod
    def isProven(stmt, assumptions=frozenset(), maxDepth=float("inf"), markProof=True):
        """
        Attempt to prove this statement under the given assumptions.  If a proof derivation
        is found, returns True.  If it can't be found in the number of steps indicated by
        maxDepth, returns False.  If qedProof is True, clear the temporary provers after
        successfully proving this statement (if not already proven).
        """
        assumptions = {asStatement(assumption) for assumption in assumptions}
        if stmt.wasProven(assumptions):
            return True
        rootProver = Prover(stmt, assumptions) 
        breadth1stQueue = [rootProver]
        while len(breadth1stQueue) > 0:
            prover = breadth1stQueue.pop(0)
            #print prover.stmtToProve, prover.depth, [assumption.getExpression() for assumption in prover.assumptions]
            if prover.isCircular(): continue
            if prover.completesProof():
                #print "tmpProvers", len(Prover._tmpProvers)
                #print "proven at depth", prover.depth
                if markProof:
                    Prover._markAsProven(stmt, rootProver)
                #if qedProof:
                #    Prover._tmpProvers.clear() # clear temporary provers after QED
                return True
            if prover.depth < maxDepth and not prover.redundant():
                prover.appendProvers(breadth1stQueue)
        return False
    
    @staticmethod
    def _markAsProven(stmt, prover):
        assumptions = prover.assumptions
        if len(assumptions) == 0 and len(stmt.freeVars()) == 0:
            # theorem-level proof
            stmt._prover = prover 
            Statement.ProofCount += 1
            stmt.proofNumber = Statement.ProofCount
            # any other provers are obsolete
            Prover._tmpProvers.pop(stmt, None)
        if not stmt in Prover._tmpProvers:
            Prover._tmpProvers[stmt] = []
        provers = Prover._tmpProvers[stmt] 
        # remove any that are made obsolete
        provers = [prover for prover in provers if assumptions.issubset(prover.assumptions)]
        if not any([prover.assumptions.issubset(assumptions) for prover in provers]):
            # only add the prover if it isn't redundant
            provers.append(prover)
        Prover._tmpProvers[stmt] = provers
    
    @staticmethod
    def getProver(stmt, assumptions):
        '''
        If this statement was proven under the given assumptions and this proof is to be
        remembered (i.e., not a clear temporary proof), returns the Prover that proves 
        this statement; otherwise, returns None.
        '''
        noAssumptionProver = stmt.getProver()
        if not noAssumptionProver is None: 
            return noAssumptionProver
        if not stmt in Prover._tmpProvers: 
            return None # no temporary provers that may prove this
        for prover in Prover._tmpProvers[stmt]:
            provenAssumptions = prover.assumptions
            if assumptions.issuperset(provenAssumptions):
                return prover
        return None
    
    @staticmethod
    def clearTemporaryProvers():
        '''
        Clear temporary Provers.  Typically done at the end of a theorem proof to clear the
        clutter of spurious assumption derivation steps.
        '''
        Prover._tmpProvers.clear()
