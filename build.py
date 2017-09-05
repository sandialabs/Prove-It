'''
Build the Prove-It notebooks (common expressions, axioms, theorems,
and proofs) for the given contexts, including sub-contexts.
'''

import sys
import os
import re
import nbformat
from nbconvert.preprocessors import ExecutePreprocessor, execute
from nbconvert import HTMLExporter
from proveit import Context

default_paths = ['packages/proveit', 'tutorial/socks_demo', 'tutorial']

def findContextPaths(path):
    if os.path.isfile(os.path.join(path, '_context_.ipynb')):
        yield path
        sub_contexts_txt = os.path.join(path, '_sub_contexts_.txt')
        if os.path.isfile(sub_contexts_txt):
            for sub_context in open(sub_contexts_txt).readlines():
                sub_context = sub_context.rstrip() # strip off the carriage return
                sub_context_path = os.path.join(path, sub_context)
                for context_path in findContextPaths(sub_context_path):
                    yield context_path

execute_processor = ExecutePreprocessor()
html_exporter = HTMLExporter()

def executeNotebook(notebook_path):
    '''
    Read and execude the notebook at the given path.
    '''
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    print 'executing', notebook_path
    sys.stdout.flush()
    execute_processor.preprocess(nb, {'metadata':{'path':os.path.split(notebook_path)[0]}})

def recordPresumingInfo(theorem, proof_notebook_path):
    '''
    Given a Theorem object and corresponding proof notebook path,
    read the 'presuming' string from the notebook (on the "%begin_proof"
    line) and record it for the theorem.
    '''
    with open(proof_notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
        for cell in nb['cells']:
            if cell['cell_type'] == 'code':
                for line in cell['source']:
                    begin_proof_str = '%begin_proof '
                    if line[:len(begin_proof_str)] == begin_proof_str:
                        presuming_str = line[line.find('['):line.find(']')]
                        theorem.recordPresumingInfo(presuming_str)
                        return # got what we needed

if __name__ == '__main__':
    # Use given paths or the defaults for the top-level contexts to be processed.
    paths = sys.argv[1:]
    if len(paths)==0:
        # use the default_paths if nothing is given
        paths = default_paths
        if os.path.sep != '/':
            # use the appropriate path separator for the OS
            paths = [path.replace('/', os.path.sep) for path in paths]
    
    # Get all the contexts of the given top-level paths
    # in the order indicated in _sub_context_.txt files.
    context_paths = []
    for path in paths:
        for context_path in findContextPaths(path):
            context_paths.append(context_path)
    
    # NOTE: NEED TO ADD CODE IN THE CORE TO DETECT MUTUAL DEPENDENCIES
    # OF COMMON NOTEBOOKS -- WE DON'T HANDLE THAT CASE HERE.
    
    # First, run the _common_.ipynb (common expression) notebooks for the contexts.
    # For any that depend up _common_.py of other contexts, run the
    # requirements first.
    common_nb_queue = list(context_paths)
    attempted_common_nb = set() # attempted but not executed
    exececuted_common_nb = set()
    while len(common_nb_queue) > 0:
        context = common_nb_queue.pop(0)
        if context in exececuted_common_nb:
            continue
        try:
            executeNotebook(os.path.join(context_path, '_common_.ipynb'))
            exececuted_common_nb.add(context) # finished successfully
        except execute.CellExecutionError as e:
            # Failed to execute _common_ notebook
            if context in attempted_common_nb:
                # coming around for a second time -- just give up
                raise e
            # Attempted but failed; if another attempt is made, give up.
            attempted_common_nb.add(context)
            common_nb_queue.insert(0, context) # re-insert to try again
            # Look for any _common_ notebooks from other contexts being imported
            # (as seen in the traceback error information) and execute those first.
            required_contexts = []
            for match in re.findall(r'([_a-zA-Z\.]*)\._common_\.ipynb', e.traceback):
                required_contexts.append(match)
            for required_context in required_contexts:
                if required_context not in exececuted_common_nb:
                    common_nb_queue.insert(0, required_context)
    
    # Second, run _axioms_.ipynb and _theorems_.ipynb notebooks for the contexts.
    # The order does not matter assuming these expression constructions
    # do not depend upon other axioms or theorems (but possibly common expressions).
    for context_path in context_paths:
        executeNotebook(os.path.join(context_path, '_axioms_.ipynb'))
        executeNotebook(os.path.join(context_path, '_theorems_.ipynb'))    

    # Get the proof notebook filenames for the theorems in all of the contexts.
    proof_notebooks = dict() # map Theorem object to corresponding proof notebooks.
    for context_path in context_paths:
        context = Context(context_path)
        for theorem_name in context.theoremNames():
            theorem = context.getTheorem(theorem_name)
            proof_notebooks[theorem] = context.proofNotebook(theorem_name, theorem.provenTruth.expr)
        
    # Third, for each of the theorems, record the "presuming" information
    # of the proof notebooks in the _proofs_ folder.  Do this before executing
    # any of the proof notebooks to account for dependencies properly
    # (avoiding circular dependencies as intended).
    for theorem, proof_notebook in proof_notebooks.iteritems():
        recordPresumingInfo(theorem, proof_notebook)
    
    # Fourth, execute all of the proof notebooks for each context.
    # the order is not important since we know the dependencies via
    # the "presuming" information from the previous step.
    for proof_notebook in proof_notebooks.values():
        executeNotebook(proof_notebook)

    # Fifth, run any other notebooks within path/context directories
    # (e.g., with tests and demonstrations).
    all_paths = list(context_paths)
    all_paths += [path for path in paths if path not in context_paths]
    for path in all_paths:
        for sub in os.listdir(path):
            full_path = os.path.join(path, sub)
            if os.path.isfile(full_path) and os.path.splitext(full_path)[1] == '.ipynb':
                if sub not in ['_common_.ipynb', '_axioms_.ipynb', '_theorems_.ipynb']:
                    executeNotebook(full_path)
        
    # Lastly, run expr.ipynb and dependencies.ipynb within the hash directories
    # of the __pv_it folders for each context.
    # May require multiple passes (showing expression info may generate
    # expr.ipynb notebooks for sub-expressions).
    executed_hash_paths = set()  # hash paths whose notebooks have been executed
    while True: # repeat until there are no more new notebooks to process
        prev_num_executed = len(executed_hash_paths)
        for path in all_paths:
            pv_it_dir = os.path.join(path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                for hash_directory in os.listdir(pv_it_dir):
                    hash_path = os.path.join(pv_it_dir, hash_directory)
                    if os.path.isdir(hash_path):
                        if hash_path in executed_hash_paths:
                            continue # already executed this case
                        expr_notebook = os.path.join(hash_path, 'expr.ipynb')
                        if os.path.isfile(expr_notebook):
                            # execute the expr.ipynb notebook
                            executeNotebook(expr_notebook)
                            executed_hash_paths.add(hash_path) # done
                        dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                        if os.path.isfile(dependencies_notebook):
                            # execute the dependencies.ipynb notebook
                            executeNotebook(dependencies_notebook)
        if len(executed_hash_paths) == prev_num_executed:
            break # no more new ones to process
