#!/bin/bash

echo "Do 'git add' on all files that have been modified but"
echo "have no change after filtering.  They will not be"
echo "staged, they will be eliminated from the 'modified' list."
echo ""

for file in `git ls-files --modified`
do
    diffresult=`git diff "$file"`
    if [ "$diffresult" == "" ]
    then
        echo "git add $file"
        git add $file
    fi
done
