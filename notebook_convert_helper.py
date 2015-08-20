import sys
import re

filename = sys.argv[1]

with open(filename) as f:
    lhs = None
    for line in f.readlines():
        line = '\n' + line
        if line.strip() == '' and lhs is not None:
            print lhs + '\n\n' # print the previous lhs
        try:
            before, lhs, rhs = re.split('\n(\S*)\s*=', line)
            if before == '':
                print lhs + ' =' + rhs.rstrip()
        except:
            pass
        
