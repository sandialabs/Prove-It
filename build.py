'''
Build the Prove-It notebooks (common expressions, axioms, theorems,
and proofs) for the given contexts, including sub-contexts.
'''

from __future__ import print_function
import sys
import os
import re
#import lxml.etree#Comment out for Python 3
import lxml#Comment in for Python 3
from lxml import etree#Comment in for Python 3
import shutil
import argparse
import nbformat
from nbconvert.preprocessors import Preprocessor, ExecutePreprocessor
from nbconvert.preprocessors.execute import executenb
from nbconvert import HTMLExporter
from IPython.lib.latextools import LaTeXTool
import base64
import datetime
import tarfile
import urllib
import tempfile
import subprocess
import zmq # to catch ZMQError which randomly occurs when starting a Jupyter kernel
from proveit import Context

# for compiling LaTeX
LaTeXTool.clear_instance()
lt = LaTeXTool.instance()
lt.use_breqn = False

default_paths = ['packages/proveit']#, 'tutorial']#, 'tutorial/socks_demo']

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

# regular expression for finding 'a' html tags; trivially adapted from
# http://haacked.com/archive/2004/10/25/usingregularexpressionstomatchhtml.aspx/
atag_re = r"""<a((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""
imgtag_re = r"""<img((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""


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
"""
def revised_special_nb(nb, notebook_path):
    # this is temporarily needed for some backwards compatibility
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'code':
            cell.source = cell.source.replace('%begin_', '%begin ')
            cell.source = cell.source.replace('%end_', '%end ')
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb
"""

class ProveItHTMLPreprocessor(Preprocessor):
    '''
    The Prove-It HTML processor will change links from ipynb
    to html and remove "target=blank".  Further, it is used to
    consolidate style information.
    '''
    
    def __init__(self, strip_links=False, make_images_inline=False):
        self.strip_links = strip_links
        self.make_images_inline = make_images_inline
        self.path = '.'
    
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
                    if atag[-2:] != b'/>':
                        raise Exception("Expecting '/>' at end of remade xml a-tag")
                    atag = atag[:-2].decode('ascii') + '>' # remove the / before >
            if not self.strip_links:
                new_text += atag
            last_pos = atag_match.end()
        new_text += text[last_pos:]
        if self.strip_links:
            return re.sub('</a>', '', new_text) # strip the </a>'s as well as the <a ...>'s
        else:
            return new_text

    def _remove_tags(self, text):
        '''
        Remove html tags from the text.
        '''
        p = re.compile(r'<.*?>')
        return p.sub('', text)
    
    """
    def _process_latex(self, text):
        '''
        Search the markdown for '$...$' indicating LaTeX.  Generate a png in place of the LaTeX.
        '''
        revised_text = ''
        cur_pos = 0
        latex_start = text.find('$')
        while latex_start >= 0:
            latex_end = text.find('$', latex_start+1)
            latex = text[latex_start+1:latex_end]
            png = latex_to_png(latex, backend='dvipng', wrap=True) # the 'matplotlib' backend can do some BAD rendering in my experience (like \lnot rendering as lnot in some contexts)
            revised_text += text[cur_pos:latex_start]
            revised_text += '<img style="vertical-align:text-bottom; display:inline;" src="data:image/png;base64,%s"/>'%base64.b64encode(png)
            cur_pos = latex_end+1
            latex_start = text.find('$', cur_pos)
        revised_text += text[cur_pos:]
        return revised_text
    """
    
    def _inline_images(self, text):
        '''
        Convert imported images to inline pngs.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for imgtag_match in re.finditer(imgtag_re, text):
            imgtag = text[imgtag_match.start():imgtag_match.end()]
            #print imgtag
            new_text += text[last_pos:imgtag_match.start()]
            # parse the img tag with a xml parser
            imgtag_root = lxml.etree.fromstring(imgtag)
            if 'src' in imgtag_root.attrib:
                png = open(os.path.join(self.path, imgtag_root.attrib['src']), 'rb').read() 
                imgtag_root.attrib['src'] = "data:image/png;base64,%s"%base64.b64encode(png)
                imgtag = lxml.etree.tostring(imgtag_root)
            #print imgtag
            new_text += imgtag
            last_pos = imgtag_match.end()
        new_text += text[last_pos:]
        return new_text
        
    def preprocess(self, nb, resources):
        new_cells = []
        empty_cells = [] # skip empty cells at the end for a cleaner look
        title = None # take the first line of the first cell to be the title
        for cell in nb.cells:
            cell = cell.copy() # copy the cell and possibly edit the copy
            if cell.cell_type == 'markdown':
                if title is None:
                    title = self._remove_tags(cell.source.split('\n')[0])
                # process a-tags in markdown cell source, as well as LaTeX.
                cell.source = self._process_atags(cell.source) #self._process_latex(self._process_atags(cell.source))
            if cell.cell_type == 'code':
                if len(cell.source)==0:
                    # an empty cell.  if it is at the end, these will be skipped altogether for a cleaner look
                    empty_cells.append(cell)
                    continue 
                if 'outputs' in cell:
                    for output in cell['outputs']:
                        if 'data' in output and 'text/html' in output.data:
                            # process a-tags in html output
                            output.data['text/html'] = self._process_atags(output.data['text/html'])
                            if self.make_images_inline:
                                # make all images inline
                                output.data['text/html'] = self._inline_images(output.data['text/html'])                                
            if len(empty_cells) > 0:
                # fill in empty cells which are not at the end
                new_cells.extend(empty_cells)
                empty_cells = []
            new_cells.append(cell)
        nb.cells = new_cells  
        resources['today'] = str(datetime.datetime.today()).split()[0]
        resources['title'] = title
        resources['up_to_index'] = '../'*self.path.count('/')
        return nb, resources

html_exporter = HTMLExporter(preprocessors=[ProveItHTMLPreprocessor()])
html_exporter.template_file = 'proveit_html'
execute_processor = ExecutePreprocessor(kernel_name='python3', timeout=-1)

def executeNotebook(notebook_path):
    '''
    Read, execute, and write out the notebook at the given path.
    Return the notebook object.
    '''
    print("Executing", notebook_path)
    
    # read
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    
    # execute using a KernelManager with the appropriate cwd (current working directory)
    notebook_dir = os.path.split(notebook_path)[0]
    resources = {'metadata':{'path':notebook_dir}}
    while True:
        try:
            #executenb(nb, cwd=notebook_dir)
            execute_processor.preprocess(nb, resources)
            break
        except zmq.ZMQError:
            print("ZMQError encountered")
            pass
            #execute_processor.km.restart_kernel(newport=True)
        except RuntimeError:
            print("Try restarting kernel")
            pass
            #execute_processor.km.restart_kernel(newport=True)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)
    return nb

def generate_css_if_missing(path):
    # check if there is a notebook.css file in the directory
    css_filename = os.path.join(path, 'notebook.css')
    if not os.path.isfile(css_filename):
        # create a notebook.css that links to a css file of the 
        # same name in the directory above it.
        with open(css_filename, 'wt') as f:
            f.write('@import url("../notebook.css")\n')

def exportToHTML(notebook_path, nb=None, strip_links=False, make_images_inline=False):
    '''
    Export the notebook to html provided the notebook path.
    The notebook object (nb) may be provided, or it will be
    read in from the file.
    '''
    print('Exporting', notebook_path, 'to HTML')
    orig_strip_links = html_exporter.preprocessors[0].strip_links
    orig_make_images_inline = html_exporter.preprocessors[0].make_images_inline
    try:
        html_exporter.preprocessors[0].strip_links = strip_links
        html_exporter.preprocessors[0].make_images_inline = make_images_inline
        html_exporter.preprocessors[0].path = os.path.split(notebook_path)[0]
        if nb is None:
            # read in if it wasn't provided
            with open(notebook_path) as f:
                nb = nbformat.read(f, as_version=4)
        # export to HTML
        (body, resources) = html_exporter.from_notebook_node(nb)
        with open(os.path.splitext(notebook_path)[0] + '.html', 'wt') as f:
            f.write(body)
        generate_css_if_missing(os.path.split(notebook_path)[0]) # add notebook.css if needed
    finally:
        html_exporter.preprocessors[0].strip_links = orig_strip_links
        html_exporter.preprocessors[0].make_images_inline = orig_make_images_inline # revert back to what it was

def executeAndExportNotebook(notebook_path, no_execute=False):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML. 
    '''
    if no_execute:
        exportToHTML(notebook_path)
    else:
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

"""
def revise_special_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_special_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)   
"""

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
    record the presuming information from information on the
    "%proving" command line.  We need to execute preceeding commands
    because some of the presumed things may be local variables generated
    in the notebook.
    '''
    with open(proof_notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    print("Record presuming info:", proof_notebook_path)
    
    # use '__' to prepend important local variables because we will start
    # running exec on user code and we don't want to pollute our locals.
    __owd = os.getcwd()
    os.chdir(os.path.split(proof_notebook_path)[0])
    __theorem = theorem
    try:
        for __cell in nb['cells']:
            if __cell['cell_type'] == 'code':
                __cellsource = __cell['source']
                __locls = locals()
                __begin_proof_str = '%proving '
                if __cellsource[:len(__begin_proof_str)] == __begin_proof_str or '\n%proving' in __cellsource:
                    __start = __cellsource.find("%proving")
                    exec(__cellsource[:__start])
                    # intercept the proving command
                    __line=__cellsource[__start+len(__begin_proof_str):]
                    __theorem_name, __presuming_str = str(__line.strip()).split(' ', 1)
                    if __theorem_name != __theorem.name:
                        raise ValueError("Theorem name, %s, does not match expectation, %s, according to filename"%(__theorem_name, theorem.name))
                    if not __presuming_str.find('presuming ') == 0:
                        raise ValueError("Bad presuming format: %s"%__presuming_str)
                    __args = __presuming_str.split(' ', 1)[-1].strip('[]').split(',')
                    __args = [__arg.strip(" \\\n") for __arg in __args]
                    __presumptions = [__arg for __arg in __args if __arg != '']
                    # Some of the presumptions are simply strings, but some are local variables
                    # we need to extract.  That is why we had to execute the previous lines.
                    __presumptions = [str(__locls[__presumption].proof()) if __presumption in __locls else __presumption for __presumption in __presumptions]
                    __theorem.provenTruth.beginProof(__theorem, __presumptions, justRecordPresumingInfo=True)
                    return
                elif __cellsource[0] != '%': # skip other magic commands (only the imports should really matter)
                    exec(__cellsource)
    finally:
        os.chdir(__owd)
    
def build(context_paths, all_paths, no_execute=False, just_execute_proofs=False, just_execute_demos=False, just_execute_expression_nbs=False):
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
    if not just_execute_proofs and not just_execute_demos and not just_execute_expression_nbs:
        # Generate html pages from index.ipynb and brief_guide.ipynb in the packages folder:
        if no_execute:
            exportToHTML('index.ipynb')
            exportToHTML('brief_guide.ipynb')
        else:
            executeAndExportNotebook('index.ipynb')
            executeAndExportNotebook('brief_guide.ipynb')
        
        # Make sure there is a _common_.py, _axioms_.py, and _theorems_.py
        # in each context directory.
        # These will be useful in figuring out dependencies between _common_
        # notebooks (see CommonExpressions in proveit._core_.context as well
        # as avoiding import errors.
        for context_path in context_paths:
            for spec_expr_kind in ('common', 'axioms', 'theorems'):
                Context(context_path).makeSpecialExprModule(spec_expr_kind)
        
        # Execute the _context_ notebooks in each context directory 
        # and generate _context_.html.
        for context_path in context_paths:
            fix_context(context_path)
            context_notebook_path = os.path.join(context_path, '_context_.ipynb')
            with open(os.path.join(context_path, '_mode_.txt'), 'wt') as f:
                f.write('interactive\n') # when executed again, it will toggle to 'static' mode                
            # execute into static mode
            executeAndExportNotebook(context_notebook_path, no_execute=no_execute)
        
        # Next, run the _common_.ipynb (common expression) notebooks for the contexts.
        # For any that depend up _common_.py of other contexts, run the
        # requirements first.
        
        """
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
        """
        
        if no_execute:
            for context_path in context_paths:
                #revise_special_notebook(os.path.join(context_path, '_common_.ipynb'))
                exportToHTML(os.path.join(context_path, '_common_.ipynb'))
        else:
            # execute the commons notebooks first, and do this twice to work out inter-dependencies
            for context_path in context_paths:
                #revise_special_notebook(os.path.join(context_path, '_common_.ipynb'))
                executeNotebook(os.path.join(context_path, '_common_.ipynb'))
            # the second time we'll export to html
            for context_path in context_paths:
                #revise_special_notebook(os.path.join(context_path, '_common_.ipynb'))
                executeAndExportNotebook(os.path.join(context_path, '_common_.ipynb'))
                    
        # Next, run _axioms_.ipynb and _theorems_.ipynb notebooks for the contexts.
        # The order does not matter assuming these expression constructions
        # do not depend upon other axioms or theorems (but possibly common expressions).
        # do this twice to get rid of extraneous information about adding/removing from database
        if no_execute:
            for context_path in context_paths:
                exportToHTML(os.path.join(context_path, '_axioms_.ipynb'))
                exportToHTML(os.path.join(context_path, '_theorems_.ipynb'))    
        else:
            for context_path in context_paths:
                #revise_special_notebook(os.path.join(context_path, '_axioms_.ipynb'))
                #revise_special_notebook(os.path.join(context_path, '_theorems_.ipynb'))
                executeNotebook(os.path.join(context_path, '_axioms_.ipynb'))
                executeNotebook(os.path.join(context_path, '_theorems_.ipynb'))    
            # the second time we'll export to html
            for context_path in context_paths:
                #revise_special_notebook(os.path.join(context_path, '_axioms_.ipynb'))
                #revise_special_notebook(os.path.join(context_path, '_theorems_.ipynb'))
                executeAndExportNotebook(os.path.join(context_path, '_axioms_.ipynb'))
                executeAndExportNotebook(os.path.join(context_path, '_theorems_.ipynb'))    
        
    if not just_execute_expression_nbs and not just_execute_demos:
        # Get the proof notebook filenames for the theorems in all of the contexts.
        proof_notebook_theorems = dict() # map proof notebook names to corresponding Theorem objects.
        theorem2notebook = dict() # map theorem to its proof notebook
        name2theorem = dict() # map theorem name to the theorem
        proof_notebooks = []
        for context_path in context_paths:
            context = Context(context_path)
            for theorem_name in context.theoremNames():
                theorem = context.getTheorem(theorem_name)
                proof_notebook_name = context.proofNotebook(theorem_name, theorem.provenTruth.expr)
                proof_notebook_theorems[proof_notebook_name] = theorem
                theorem2notebook[theorem] = proof_notebook_name
                name2theorem[str(theorem)] = theorem
                proof_notebooks.append(proof_notebook_name)
        
        if no_execute:
            for proof_notebook in proof_notebooks:
                #if not os.path.isfile(proof_notebook[-5:] + '.html'): # temporary
                exportToHTML(proof_notebook)
        else:
            # Next, for each of the theorems, record the "presuming" information
            # of the proof notebooks in the _proofs_ folder.  Do this before executing
            # any of the proof notebooks to account for dependencies properly
            # (avoiding circular dependencies as intended).
            for proof_notebook in proof_notebooks:
                recordPresumingInfo(proof_notebook_theorems[proof_notebook], proof_notebook)
                
            # Next, execute all of the proof notebooks twice
            # to ensure there are no circular logic violations.
            for proof_notebook in proof_notebooks:
                executeNotebook(proof_notebook)
            for proof_notebook in proof_notebooks:
                executeAndExportNotebook(proof_notebook)
            
    if not just_execute_expression_nbs:
        # Next, run any other notebooks within path/context directories
        # (e.g., with tests and demonstrations).
        for path in all_paths:
            for sub in os.listdir(path):
                full_path = os.path.join(path, sub)
                if os.path.isfile(full_path) and os.path.splitext(full_path)[1] == '.ipynb':
                    if sub == '_demonstrations_.ipynb': #or sub[0] != '_': # temporarily exclude other notebooks
                        executeAndExportNotebook(full_path, no_execute=no_execute)
        
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
                        expr_html = os.path.join(hash_path, 'expr.html')
                        expr_notebook = os.path.join(hash_path, 'expr.ipynb')
                        if os.path.isfile(expr_notebook):
                            if no_execute:
                                exportToHTML(expr_notebook)
                            else:
                                # if expr_html doesn't exist or is older than expr_notebook, generate it
                                if not os.path.isfile(expr_html) or os.path.getmtime(expr_html) < os.path.getmtime(expr_notebook):
                                    # execute the expr.ipynb notebook
                                    executeAndExportNotebook(expr_notebook)
                                    executed_hash_paths.add(hash_path) # done
                        # always execute the dependencies notebook for now to be safes
                        dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                        if os.path.isfile(dependencies_notebook):
                            # execute the dependencies.ipynb notebook
                            executeAndExportNotebook(dependencies_notebook, no_execute=no_execute)
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
    parser.add_argument('--download', dest='download', action='store_const',
                        const=True, default=False,
                        help='download and extract the tarball of __pv_it directories from http://pyproveit.org')    
    parser.add_argument('--justproofs', dest='just_execute_proofs', action='store_const',
                        const=True, default=False,
                        help='only execute proofs (not _common_, _axioms_, or _theorems_)')   
    parser.add_argument('--justdemos', dest='just_execute_demos', action='store_const',
                        const=True, default=False,
                        help='only execute demonstration (not _common_, _axioms_, _theorems_, or proofs)')   
    parser.add_argument('--justexpressions', dest='just_execute_expression_nbs', action='store_const',
                        const=True, default=False,
                        help='only execute expression notebooks')   
    parser.add_argument('--noexecute', dest='noexecute', action='store_const',
                        const=True, default=False,
                        help='do not execute notebooks, just convert to HTML')   
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
        print("Cleaning '__pv_it' directories...")
        sys.stdout.flush()
        for path in all_paths:
            # remove the __pv_it folders from all paths
            pv_it_dir = os.path.join(path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                shutil.rmtree(pv_it_dir)
    elif not args.download:
        # remove the __pv_it/commons.pv_it in all of the context paths
        # to make sure everything gets updated where there are dependencies
        # between common expressions of different contexts.
        for path in context_paths:
            generate_css_if_missing(path)
            pv_it_dir = os.path.join(path, '__pv_it')
            generate_css_if_missing(pv_it_dir)
            if os.path.isdir(pv_it_dir):
                commons_filename = os.path.join(pv_it_dir, 'commons.pv_it')
                if os.path.isfile(commons_filename):
                    os.remove(commons_filename) 
        build(context_paths, all_paths, args.noexecute, args.just_execute_proofs, args.just_execute_demos, args.just_execute_expression_nbs)
    
    if args.download:
        '''
        Download and extract the tarball of __pv_it directories.
        '''
        if not args.clean:
            raise ValueError("The '--download' option is currently only implemented to work in conjunction with the '--clean' option")
        if args.noexecute or args.just_execute_proofs or args.just_execute_demos or args.just_execute_expression_nbs:
            raise ValueError("Do not combine the '--download' option with any other option besides '--clean'")
        url = "http://pyproveit.org/pv_it.tar.gz" # tarball url
        print("Downloading '%s'"%url)
        file_tmp = urllib.request.urlretrieve(url, filename=None)[0]
        tar = tarfile.open(file_tmp)
        # extract into the directory of this 'build.py'
        path = os.path.dirname(os.path.realpath(__file__))
        print("Extracting tarball into %s"%path)
        tar.extractall(path)
