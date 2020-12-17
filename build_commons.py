'''
Build the Prove-It common expression notebooks for the given theories, 
including sub-theories.
'''

from build import (default_paths, find_theory_paths, 
                   notebook_path_generator, mpi_build)
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
                        help='paths to be processed; sub-theories will be included recursively (default: %s)'%' '.join(default_paths))
    args = parser.parse_args()    
    paths = args.path

    try:
        from mpi4py import MPI
        comm = MPI.COMM_WORLD
        rank = comm.Get_rank()
        nranks = comm.Get_size()
    except:
        rank, nranks = 0, 1
    
    if rank==0:
        # First remove the __pv_it/common/name_to_hash.txt files to make
        # sure we are using the correct version of the common expressions.
        for path in paths:
            for theory_path in find_theory_paths(path):
                name_to_hash_filename = os.path.join(
                    theory_path, '__pv_it', 'common', 'name_to_hash.txt')
                if os.path.isfile(name_to_hash_filename):
                    os.remove(name_to_hash_filename)
    if nranks > 1:
        comm.barrier()
    
    mpi_build(notebook_path_generator(paths, '_common_.ipynb'), 
              no_latex=args.nolatex, git_clear=not args.nogitclear, 
              no_execute=args.noexecute, export_to_html=True)