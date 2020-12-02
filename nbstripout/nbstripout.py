'''
Removes the "output" from notebooks for the purpose of git filtering.

Adapted from fastai-nbstripout:
https://github.com/fastai/fastai-nbstripout/tree/master/tools

fast-nbstripout was inspired by nbstripout but manipulates the json 
directly instead of via nbformat to make the filtering more efficient.
This code was adapted from fastai-nbstripout but simplified (not
using their 'doc' variant) and slightly modified 
(setting 'nbformat_minor' to 0 to avoid committing minor format
changes).
'''

import io, sys, argparse, json

# define which fields need to be kept:
cell_metadata_keep = []
nb_metadata_keep   = ['kernelspec', 'jekyll']

### filter for code nb cells ###
# 1. reset execution_count
# 2. delete cell's metadata
# 3. delete cell's outputs

def clean_cell(o):
    if 'execution_count' in o: o['execution_count'] = None
    if 'outputs'         in o: o['outputs']         = []
    o['metadata'] = { k:o['metadata'][k] for k in o['metadata'].keys() if k in cell_metadata_keep }
    return o

### filter for nb top level entries ###
# 1. keep only nb_metadata_keep fields
# 2. the other rules apply based on clean_cell alias

def clean_nb(input_stream):
    s = json.load(input_stream)
    s['cells']    = [ clean_cell(o) for o in s['cells'] ]
    s['metadata'] = { k:s['metadata'][k] for k in s['metadata'].keys() if k in nb_metadata_keep }
    # Hopefully the minor format won't matter and we can use the lowest common denominator for now:
    s['nbformat_minor'] = 0
    if 'language_info' in s:
        # Just remove the 'language_info' to keep the notebooks
        # consistent.
        s.pop('language_info')
    return json.dumps(s, sort_keys=True, indent=1, ensure_ascii=False)

if __name__ == '__main__':
    if sys.stdin: input_stream = io.TextIOWrapper(sys.stdin.buffer, encoding='utf-8')
    output_stream = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

    parser = argparse.ArgumentParser()
    parser.add_argument('-t', '--textconv', action="store_true", help="Print results to output")
    parser.add_argument('files', nargs='*', help='Files to strip output from')
    args = parser.parse_args()
    

    for filename in args.files:
        if not filename.endswith('.ipynb'): continue
        with io.open(filename, 'r', encoding='utf-8') as f: 
            x = clean_nb(f)
        
        if args.textconv:
            # XXX: if there is more than one file, this is probably wrong
            output_stream.write(x)
            output_stream.write("\n")
            output_stream.flush()
        else:
            with io.open(filename, 'w', encoding='utf-8') as f:
                f.write(x)
                f.write("\n")
    
    # implied textconv mode
    if not args.files and input_stream:
        x = clean_nb(input_stream)
        output_stream.write(x)
        output_stream.write("\n")
        output_stream.flush()
    
