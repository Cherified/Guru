#!/usr/bin/env python3
import sys

for line in sys.stdin:
    if len(line) <= 200:
        sys.stdout.write(line)
        continue
    indent = ' ' * (len(line) - len(line.lstrip()) + 2)
    s = line.rstrip('\r\n')
    while len(s) > 200:
        idx = s.find(' ', 200)
        if idx == -1:
            break
        sys.stdout.write(s[:idx] + '\n' + indent)
        s = s[idx + 1:]
    sys.stdout.write(s + '\n')
