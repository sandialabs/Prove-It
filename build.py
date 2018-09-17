'''
Build the Prove-It notebooks (common expressions, axioms, theorems,
and proofs) for the given contexts, including sub-contexts.
'''

import sys
import os
import re
import lxml.etree
import shutil
import argparse
import nbformat
from nbconvert.preprocessors import ExecutePreprocessor, execute, Preprocessor
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

execute_processor = ExecutePreprocessor(timeout=1000)

# regular expression for finding 'a' html tags; trivially adapted from
# http://haacked.com/archive/2004/10/25/usingregularexpressionstomatchhtml.aspx/
atag_re = r"""<a((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""

def _fix_atags(text):
    '''
    Temporary use: fix a-tags missing class="ProveIt"
    '''
    new_text = ''
    last_pos = 0
    text = str(text)
    for atag_match in re.finditer(atag_re, text):
        atag = text[atag_match.start():atag_match.end()]
        new_text += text[last_pos:atag_match.start()]
        # parse the a tag with a xml parser
        atag_root = lxml.etree.fromstring(atag + '</a>')
        if atag_root.attrib['href'] == '_context_.html':
            atag_root.attrib['href'] == '_context_.ipynb' # fix a mistake in earlier templates
        href_split_ext = os.path.splitext(atag_root.attrib['href'])
        if '.ipynb' in href_split_ext[1]:
            atag_root.attrib['class']='ProveItLink'
        atag = lxml.etree.tostring(atag_root)[:-2] + '>'
        new_text += atag
        last_pos = atag_match.end()
    new_text += text[last_pos:]
    return new_text

def revised(nb):
    '''
    Temporary use to fix a-tags
    '''
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'markdown':
            # process a-tags in markdown cell source
            cell.source = _fix_atags(cell.source)
        if cell.cell_type == 'code':
            if 'outputs' in cell:
                for output in cell['outputs']:
                    if 'data' in output and 'text/html' in output.data:
                        # process a-tags in html output
                        output.data['text/html'] = _fix_atags(output.data['text/html'])
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb

"""
def revised_proof_nb(nb, notebook_path):
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'markdown':
            cell.source = cell.source.replace('\\\\', '\\')
            cell.source = cell.source.replace('\\"', '"')
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb
"""
def revised_special_nb(nb, notebook_path):
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'code':
            cell.source = cell.source.replace('%begin_', '%begin ')
            cell.source = cell.source.replace('%end_', '%end ')
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb

class ProveItHTMLPreprocessor(Preprocessor):
    '''
    The Prove-It HTML processor will change links from ipynb
    to html and remove "target=blank".
    '''
    
    def _process_atags(self, text):
        '''
        Search the text for html a-tags of the ProveItLink class.
        For each of these, replace .ipynb with .html and remove 
        any target='_blank' (so it does not create a new tab 
        in the browser).  Return the new version of the text.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for atag_match in re.finditer(atag_re, text):
            atag = text[atag_match.start():atag_match.end()]
            new_text += text[last_pos:atag_match.start()]
            # parse the a tag with a xml parser
            atag_root = lxml.etree.fromstring(atag + '</a>')
            if 'class' in atag_root.attrib and atag_root.attrib['class']=='ProveItLink':
                if '.ipynb' in atag_root.attrib['href']:
                    # replace the .ipynb extension in the href with .html
                    atag_root.attrib['href'] = atag_root.attrib['href'].replace('.ipynb', '.html')
                    # also, if the .ipynb link uses target='blank', nix that.
                    if 'target' in atag_root.attrib and atag_root.attrib['target']=='_blank':
                        atag_root.attrib.pop('target')
                    atag = lxml.etree.tostring(atag_root)
                    if atag[-2:] != '/>':
                        raise Exception("Expecting '/>' at end of remade xml a-tag")
                    atag = atag[:-2] + '>' # remove the / before >
            new_text += atag
            last_pos = atag_match.end()
        new_text += text[last_pos:]
        return new_text
    
    def preprocess(self, nb, resources):
        new_cells = []
        for cell in nb.cells:
            cell = cell.copy() # copy the cell and possibly edit the copy
            if cell.cell_type == 'markdown':
                # process a-tags in markdown cell source
                cell.source = self._process_atags(cell.source)
            if cell.cell_type == 'code':
                if 'outputs' in cell:
                    for output in cell['outputs']:
                        if 'data' in output and 'text/html' in output.data:
                            # process a-tags in html output
                            output.data['text/html'] = self._process_atags(output.data['text/html'])
            new_cells.append(cell)
        nb.cells = new_cells            
        return nb, resources

html_exporter = HTMLExporter(preprocessors=[ProveItHTMLPreprocessor()])

def executeNotebook(notebook_path):
    '''
    Read, execute, and write out the notebook at the given path.
    Return the notebook object
    '''
    print 'Executing', notebook_path
    sys.stdout.flush()
    # read
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
        
    # do some temporary fixes
    nb = revised(nb)
    
    # execute
    execute_processor.preprocess(nb, {'metadata':{'path':os.path.split(notebook_path)[0]}})
    # write notebook
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)
    return nb

def exportToHTML(notebook_path, nb=None):
    '''
    Export the notebook to html provided the notebook path.
    The notebook object (nb) may be provided, or it will be
    read in from the file.
    '''
    if nb is None:
        # read in if it wasn't provided
        with open(notebook_path) as f:
            nb = nbformat.read(f, as_version=4)
    # export to HTML
    (body, resources) = html_exporter.from_notebook_node(nb)
    with open(os.path.splitext(notebook_path)[0] + '.html', 'wt') as f:
        f.write(body)

def executeAndExportNotebook(notebook_path):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML. 
    '''
    nb = executeNotebook(notebook_path)
    exportToHTML(notebook_path, nb)

"""
def revise_proof_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_proof_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)        
"""

def revise_special_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_special_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)   

def fix_context(context_path):
    mode = None
    with open(os.path.join(context_path, '_sub_contexts_.txt')) as f:
        sub_context_names = []
        for k, line in enumerate(f.readlines()):
            if k==0 and line[:6] == 'mode: ':
                mode = line[6:].strip()
            else:
                sub_context_names.append(line.strip())
        Context(context_path).setSubContextNames(sub_context_names)
    if mode is not None:
        with open(os.path.join(context_path, '_mode_.txt'), 'w') as fw:
            fw.write(mode + '\n')

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
                for line in cell['source'].split('\n'):
                    begin_proof_str = '%begin_proof '
                    if line[:len(begin_proof_str)] == begin_proof_str:
                        theorem_name, presuming_str = str(line.strip()).split(' ', 1)
                        args = line[line.find('[')+1:line.find(']')].split(',')
                        presuming = [arg.strip() for arg in args if arg.strip() != '']
                        theorem.recordPresumingInfo(presuming)
                        return # got what we needed
    
def build(context_paths, all_paths, just_execute_proofs=False):
    '''
    Build all Context-related notebooks (_common_, _axioms_,
    _theorems_, and proof notebooks for the theorems)
    in the context_paths.
    For the paths in all_paths (which should include the
    context paths), build any contained notebooks and
    any of the expr.ipynb and dependencies.ipnyb notebooks
    within the __pv_it directory (storing Prove-It "database"
    information).
    '''
    if not just_execute_proofs:
        # Make sure there is a _common_.py in each context directory.
        # These will be useful in figuring out dependencies between _common_
        # notebooks (see CommonExpressions in proveit._core_.context
        for context_path in context_paths:
            Context(context_path).makeSpecialExprModule('common')
        
        # Execute the _context_ notebooks in each context directory as
        # needed and generate _context_.html.
        for context_path in context_paths:
            fix_context(context_path)
            context_notebook_path = os.path.join(context_path, '_context_.ipynb')
            with open(os.path.join(context_path, '_mode_.txt')) as f:
                prev_mode = f.read().strip()
                
            if prev_mode=='interactive':
                # re-execute to get switch it to static mode
                executeAndExportNotebook(context_notebook_path)
            else:
                # don't re-execute the notebook because it is already in
                # static mode; just export it to HTML.
                exportToHTML(context_notebook_path)
        
        # Next, run the _common_.ipynb (common expression) notebooks for the contexts.
        # For any that depend up _common_.py of other contexts, run the
        # requirements first.
        common_nb_queue = list(context_paths)
        exececuted_common_nb = set()
        while len(common_nb_queue) > 0:
            context_path = common_nb_queue.pop(0)
            if context_path in exececuted_common_nb:
                continue
            
            # The failed_common_import.txt file is used to communicate a failed
            # common expression import from another context.  First erase this
            # file, then see if it is created after executing the common notebook.
            failed_common_import_filename = os.path.join(context_path, '__pv_it', 'failed_common_import.txt')
            if os.path.isfile(failed_common_import_filename):
                os.remove(failed_common_import_filename)
                
            try:
                revise_special_notebook(os.path.join(context_path, '_common_.ipynb'))
                executeAndExportNotebook(os.path.join(context_path, '_common_.ipynb'))
                exececuted_common_nb.add(context_path) # finished successfully
            except execute.CellExecutionError as e:            
                retry = False
                if os.path.isfile(failed_common_import_filename):
                    # A failed_common_import.txt file was created.  It will indicate the
                    # context from which a common expression was attempted to be imported.
                    # If its _common_ notebook has not already executed, execute it first
                    # and then try to execute this one again.
                    with open(failed_common_import_filename, 'r') as f:
                        required_context_name = f.read().strip()
                        if required_context_name not in exececuted_common_nb:
                            print '  Failed to execute; try a prerequisite first:', required_context_name
                            common_nb_queue.insert(0, context_path) # re-insert to try again
                            # but first execute the _common_ notebook from the required_context.
                            common_nb_queue.insert(0, context_map[required_context_name])
                            retry = True
                if not retry:
                    raise e
            
        # Next, run _axioms_.ipynb and _theorems_.ipynb notebooks for the contexts.
        # The order does not matter assuming these expression constructions
        # do not depend upon other axioms or theorems (but possibly common expressions).
        for context_path in context_paths:
            revise_special_notebook(os.path.join(context_path, '_axioms_.ipynb'))
            revise_special_notebook(os.path.join(context_path, '_theorems_.ipynb'))
            executeAndExportNotebook(os.path.join(context_path, '_axioms_.ipynb'))
            executeAndExportNotebook(os.path.join(context_path, '_theorems_.ipynb'))    
    
    # Get the proof notebook filenames for the theorems in all of the contexts.
    proof_notebook_theorems = dict() # map proof notebook names to corresponding Theorem objects.
    proof_notebooks = []
    for context_path in context_paths:
        context = Context(context_path)
        for theorem_name in context.theoremNames():
            theorem = context.getTheorem(theorem_name)
            proof_notebook_name = context.proofNotebook(theorem_name, theorem.provenTruth.expr)
            proof_notebook_theorems[proof_notebook_name] = theorem
            proof_notebooks.append(proof_notebook_name)
        
    # Next, for each of the theorems, record the "presuming" information
    # of the proof notebooks in the _proofs_ folder.  Do this before executing
    # any of the proof notebooks to account for dependencies properly
    # (avoiding circular dependencies as intended).
    for proof_notebook in proof_notebooks:
        print 'record presuming info:', proof_notebook
        recordPresumingInfo(proof_notebook_theorems[proof_notebook], proof_notebook)
        
    # Next, execute all of the proof notebooks for each context.
    # the order is not important since we know the dependencies via
    # the "presuming" information from the previous step.
    for proof_notebook in proof_notebooks:
        executeAndExportNotebook(proof_notebook)
        
    # Next, run any other notebooks within path/context directories
    # (e.g., with tests and demonstrations).
    for path in all_paths:
        for sub in os.listdir(path):
            full_path = os.path.join(path, sub)
            if os.path.isfile(full_path) and os.path.splitext(full_path)[1] == '.ipynb':
                if sub[0] != '_':
                    executeAndExportNotebook(full_path)
        
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
                            executeAndExportNotebook(expr_notebook)
                            executed_hash_paths.add(hash_path) # done
                        dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                        if os.path.isfile(dependencies_notebook):
                            # execute the dependencies.ipynb notebook
                            executeAndExportNotebook(dependencies_notebook)
        if len(executed_hash_paths) == prev_num_executed:
            break # no more new ones to process
    
if __name__ == '__main__':
    if os.path.sep != '/':
        # use the appropriate path separator for the OS
        default_paths = [path.replace('/', os.path.sep) for path in default_paths]
        
    # parse the arguments and provide help information.
    parser = argparse.ArgumentParser(description='Build all of the Prove-It notebooks in selected directories.')
    parser.add_argument('--clean', dest='clean', action='store_const',
                        const=True, default=False,
                        help='remove all of the autogenerated __pv_it directories')    
    parser.add_argument('--justproofs', dest='just_execute_proofs', action='store_const',
                        const=True, default=False,
                        help='only execute proofs (not _common_, _axioms_, or _theorems_)')   
    parser.add_argument('path', type=str, nargs='*', default=default_paths,
                        help='paths to be processed; sub-contexts will be included recursively (default: %s)'%' '.join(default_paths))
    args = parser.parse_args()    
    paths = args.path
        
    # Get all the contexts of the given top-level paths
    # in the order indicated in _sub_context_.txt files.
    context_paths = []
    context_map = dict() # map Context names to paths
    for path in paths:
        for context_path in findContextPaths(path):
            context_paths.append(context_path)
            context_map[Context(context_path).name] = context_path
    
    all_paths = list(context_paths)
    all_paths += [path for path in paths if path not in context_paths]

    if args.clean:
        # clean all of the __pv_it directories that may be auto-generated
        print "Cleaning '__pv_it' directories..."
        sys.stdout.flush()
        for path in all_paths:
            # remove the __pv_it folders from all paths
            pv_it_dir = os.path.join(path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                shutil.rmtree(pv_it_dir)
    else:
        # remove the __pv_it/commons.pv_it in all of the context paths
        # to make sure everything gets updated where there are dependencies
        # between common expressions of different contexts.
        for path in context_paths:
            pv_it_dir = os.path.join(path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                commons_filename = os.path.join(pv_it_dir, 'commons.pv_it')
                if os.path.isfile(commons_filename):
                    os.remove(commons_filename) 
        build(context_paths, all_paths, args.just_execute_proofs)
        