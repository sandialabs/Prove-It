#!/usr/bin/env python

"""
Suppress output and prompt numbers in git version control.

This script will tell git to ignore prompt numbers and cell output
when looking at ipynb files.

The notebooks themselves are not changed.

See also this blogpost: http://pascalbugnion.net/blog/ipython-notebooks-and-git.html.

Usage instructions
==================

1. Put this script in a directory that is on the system's path.
   For future reference, I will assume you saved it in 
   `~/scripts/ipynb_drop_output`.
2. Make sure it is executable by typing the command
   `chmod +x ~/scripts/ipynb_drop_output`.
3. Register a filter for ipython notebooks by
   putting the following line in `~/.config/git/attributes`:
   `*.ipynb  filter=clean_ipynb`
4. Connect this script to the filter by running the following 
   git commands:

   git config --global filter.clean_ipynb.clean ipynb_drop_output
   git config --global filter.clean_ipynb.smudge cat

Notes
=====

This script is inspired by http://stackoverflow.com/a/20844506/827862 and
adapted from https://gist.github.com/pbugnion/ea2797393033b54674af.
"""

import sys
import json

nb = sys.stdin.read()

json_in = json.loads(nb)

ipy_version = int(json_in["nbformat"])-1 # nbformat is 1 more than actual version.

def strip_output_from_cell(cell):
    if "outputs" in cell:
        cell["outputs"] = []
    if "prompt_number" in cell:
        del cell["prompt_number"]
    if "execution_count" in cell:
        cell["execution_count"] = None

for cell in json_in["cells"]:
    strip_output_from_cell(cell)

json.dump(json_in, sys.stdout, sort_keys=True, indent=1, separators=(",",": "))

