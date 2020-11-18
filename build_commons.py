'''
Build the Prove-It common expression notebooks for the given contexts, 
including sub-contexts.
'''

from build import default_paths, notebook_path_generator, mpi_build
import os
import argparse

if __name__ == '__main__':
    if os.path.sep != '/':
        # use the appropriate path separator for the OS
        default_paths = [path.replace('/', os.path.sep) for path in default_paths]
        
    # parse the arguments and provide help information.
    parser = argparse.ArgumentParser(description='Build all of the Prove-It notebooks in selected directories.')
    parser.add_argument('--clean', dest='clean', action='store_const',
                        const=True, default=False,
                        help='remove all of the autogenerated __pv_it directories')    
    parser.add_argument('--nolatex', dest='nolatex', action='store_const',
                        const=True, default=False,
                        help='speed execution by skipping LaTeX generation')   
    parser.add_argument('--nogitclear', dest='nogitclear', action='store_const',
                        const=True, default=False,
                        help='do not bother doing "git add" to clear git of notebooks whose modifications are only in filtered output')   
    parser.add_argument('--noexecute', dest='noexecute', action='store_const',
                        const=True, default=False,
                        help='do not execute notebooks, just convert to HTML')   
    parser.add_argument('--nohtml', dest='nohtml', action='store_const',
                        const=True, default=False,
                        help='do not export notebooks to HTML, just execute them')   
    parser.add_argument('path', type=str, nargs='*', default=default_paths,
                        help='paths to be processed; sub-contexts will be included recursively (default: %s)'%' '.join(default_paths))
    args = parser.parse_args()    
    paths = args.path
    
    mpi_build(notebook_path_generator(paths, '_common_.ipynb'), 
              no_latex=args.nolatex, git_clear=not args.nogitclear, 
              no_execute=args.noexecute, export_to_html=True)
