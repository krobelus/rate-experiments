#!/usr/bin/env python3

import os, subprocess
from subprocess import check_output
from math import floor

INPUT = 'g12.cnf'
def interesting():
    return 0 == os.system("rupee g12.cnf g12.drat | grep -qxF 'Error: broken invariant.'")

def x(s):
    if 0:
        print(s)
    if 1:
        assert 0 == os.system(s)

# start = 930 + 3
start = 26
lines = int(check_output(f'wc -l < {INPUT}', shell=True).rstrip())
current = start

x(f'cp {INPUT} {INPUT}.bak')

while current < lines:
    # chunk = max(1, floor(lines / 20))
    chunk = 1
    maxintidx = 'init'
    while current < lines:
        print(f'line: {current}/{lines} removing: {chunk}, maxintidx: {maxintidx}')
        # input()
        x(f'sed {current},{current + chunk}d -i {INPUT}')
        if maxintidx != 'init':
            maxintidx -= chunk
            lines -= chunk
        if interesting():
            print('interesting')
            x(f'cp {INPUT} {INPUT}.bak')
            if maxintidx == 'init':
                chunk *= 2
            else:
                if chunk == 1:
                    pass
                else:
                    chunk = floor(maxintidx / 2)
        else:
            print('not interesting')
            x(f'cp {INPUT}.bak {INPUT}')
            if maxintidx != 'init':
                maxintidx += chunk
                lines += chunk
            if chunk == 1:
                '''
                the deleted line is essential for the formula to be interesting
                skip deleting it from now on
                '''
                current += 1
                break
            else:
                if maxintidx == 'init':
                    maxintidx = chunk
                    chunk = floor(chunk / 2)
                else:
                    maxintidx = chunk
                    chunk = floor(chunk / 2)

print(lines)
