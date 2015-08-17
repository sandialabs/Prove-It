import sys
import re

filename = sys.argv[1]

with open(filename) as f:
    for line in f.readlines():
        line = '\n' + line
        try:
            before, lhs, rhs = re.split('\n(\S*)\s*=', line)
            if before == '':
                print lhs + ' =' + rhs.rstrip()
                print lhs + '\n'
        except:
            pass
        
