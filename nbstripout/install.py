'''
Perform the git configuration and attribute changes needed to filter
the output of jupyter notebooks.  This is taken from
https://github.com/kynan/nbstripout/blob/master/nbstripout/_nbstripout.py
with minimal changes.
'''

import sys


def install_nbstripout(git_config, attrfile=None):
    """Install the git filter and set the git attributes."""
    from os import name, path
    from subprocess import check_call, check_output, CalledProcessError
    try:
        git_dir = check_output(['git', 'rev-parse', '--git-dir']).strip()
    except (WindowsError if name == 'nt' else OSError):
        print('Installation failed: git is not on path!', file=sys.stderr)
        sys.exit(1)
    except CalledProcessError:
        print('Installation failed: not a git repository!', file=sys.stderr)
        sys.exit(1)
    dir = path.abspath(path.dirname(__file__))
    filepath = '"{}" "{}"'.format(
        sys.executable, path.join(
            dir, 'nbstripout.py')).replace(
        '\\', '/')
    check_call(git_config + ['filter.nbstripout.clean', filepath])
    check_call(git_config + ['filter.nbstripout.smudge', 'cat'])
    check_call(git_config + ['diff.ipynb.textconv', filepath + ' -t'])

    if not attrfile:
        attrfile = path.join(git_dir.decode(), 'info', 'attributes')
    attrfile = path.expanduser(attrfile)

    # Check if there is already a filter for ipynb files
    filt_exists = False
    diff_exists = False
    if path.exists(attrfile):
        with open(attrfile, 'r') as f:
            attrs = f.read()
        filt_exists = '*.ipynb filter' in attrs
        diff_exists = '*.ipynb diff' in attrs
        if filt_exists and diff_exists:
            return

    with open(attrfile, 'a') as f:
        # If the file already exists, ensure it ends with a new line
        if f.tell():
            f.write('\n')
        if not filt_exists:
            print('*.ipynb filter=nbstripout', file=f)
        if not diff_exists:
            print('*.ipynb diff=ipynb', file=f)


if __name__ == '__main__':
    install_nbstripout(['git', 'config'], '.gitattributes')
