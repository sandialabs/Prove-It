#!/bin/bash

echo "Do 'git add' on all files that have been modified but"
echo "have no change after filtering.  They will not be"
echo "staged, they will be eliminated from the 'modified' list."
echo ""

for file in `git ls-files --modified`
do
    # Piping the git diff command through sed is necessary
    # when nbdime is installed and configured for git.  In
    # that case "git diff ..." reports the alternate command
    # it is running as the first line.
    diffresult=`git diff "$file" | sed "s/^diff --git .*$//g"`
    if [ "$diffresult" == "" ]
    then
        echo "git add $file"
        git add $file
    fi
done
