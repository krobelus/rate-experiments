#!/usr/bin/env python3

import sys, os, subprocess
from subprocess import check_output
from math import floor

name = sys.argv[1]
start = int(sys.argv[2])

CNF = f'{name}.cnf'
INPUT = f'{name}.drat'
def interesting():
    return 0 == os.system("rate g.cnf g.drat 2>&1|grep -q assertion.failed:.left.position")

DEBUG = 0

def x(s):
    if DEBUG:
        print(s)
    else:
        assert 0 == os.system(s)

lines = int(check_output(f'wc -l < {INPUT}', shell=True).rstrip())
current = start

x(f'cp {CNF} {CNF}.bak')
x(f'cp {INPUT} {INPUT}.bak')

while current < lines:
    # chunk = max(1, floor(lines / 20))
    # chunk = max(1, floor((lines - current) / 33))
    chunk = 1
    maxintidx = 'init'
    while current < lines:
        print(f'line: {current}/{lines} removing: {chunk}, maxintidx: {maxintidx}')
        # print('cont?', end=''); input()
        x(f'sed {current},{current + chunk}p -n {INPUT} | sed "/^d /d" >> {CNF}')
        x(f'sed {current},{current + chunk}d -i {INPUT}')
        if maxintidx != 'init':
            maxintidx -= chunk
        lines -= chunk
        if interesting():
            print('interesting')
            x(f'cp {INPUT} {INPUT}.bak')
            x(f'cp {CNF} {CNF}.bak')
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
            x(f'cp {CNF}.bak {CNF}')
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
