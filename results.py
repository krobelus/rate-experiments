#!/usr/bin/env python3

import os
import sys
import json
import re


def dimensions():
    with open('checkers.txt') as f:
        checkers = [line.strip() for line in f]
    with open('solvers.txt') as f:
        solvers = [line.strip() for line in f]
    with open('instances.txt') as f:
        instances = [instance.strip() for instance in f if instance.strip()]
    return checkers, solvers, instances


def si(solver, instance):
    return os.path.abspath('./benchmarks/%s/%s' % (instance, solver))


def checker_stats(checker, path):
    if checker == 'gratgen':
        return stats('%s/stderr' % path)
    return stats('%s/stdout' % path)


def stats(path):
    if not os.path.exists(path):
        return {}
    with open(path) as f:
        lines = list(f)
    return {
        m.group(1): m.group(2)
        for m in (re.search(r'c ([a-zA-Z\-\ ]+): \s*(.*)', line) for line in lines)
        if m is not None
    }


def checker_solution(checker, path):
    if checker == 'gratgen':
        return solution('%s/stderr' % path)
    return solution('%s/stdout' % path)


def solution(path, *, solver=None):
    if not os.path.exists(path):
        return 'n/a'
    with open(path) as f:
        solutions = []
        if solver == 'expGlucose@default':
            solutions = (line[1:].strip() for line in f
                         if line.startswith(' UNSATISFIABLE'))
        if solutions == []:
            solutions = (line[2:].strip() for line in f
                         if line.startswith('s ') or line.startswith('\rs '))
        return next(solutions, 'error')


def runlim(path):
    def remove_units(s):
        for unit in ('seconds', 'MB'):
            s = s.replace(' %s' % unit, '')
        return s

    if not os.path.exists(path):
        return []
    with open(path) as f:
        tuples = [[
            remove_units(value).strip()
            for value in line[len('[runlim] '):].split(":", maxsplit=1)
        ] for line in f]
    return tuples


def summarize_checker_result(checker):
    if 'status' not in checker:
        return 'n/a'
    if checker['status'] == 'out of memory':
        return 'out of memory'
    if checker['status'] == 'out of time' or (
            'drat-trim' in checker['checker']
            and checker['solution'] == 'TIMEOUT'):
        return 'out of time'
    if checker['status'] == 'ok':
        if checker['solution'] in ('VERIFIED', 'ACCEPTED'):
            if checker['verified'] == 'VERIFIED' or checker[
                    'checker'] == 'gratgen':  # TODO gratchk
                return 'verified'
            if checker['verified'] == 'n/a':
                return 'lrat-check pending'
            if checker['verified'] == 'error':
                return 'lrat-check failed'
            assert False, 'unexpected lrat-check solution: "%s"' % checker[
                'verified']
        if ('gratgen' in checker['checker'] and checker['solution'] == 'ERROR'
                or checker['solution'] in ('NOT VERIFIED', 'REJECTED')):
            return 'rejected'
        if checker['solution'] == 'error':
            return 'error'
        assert False, 'unexpected checker solution: "%s"' % checker['solution']
    # TODO FIXME
    if checker['status'] == 'segmentation fault':
        return 'segmentation fault'
    assert False, 'unexpected runlim status: "%s"' % checker['status']


def results():
    checkers, solvers, instances = dimensions()
    data = [{
        'instance':
        instance,
        'solvers': [
            dict([('solver', solver),
                  ('solution',
                   solution('%s/stdout' % si(solver, instance), solver=solver)
                   )] + runlim('%s/runlim.out' % si(solver, instance)) +
                 [('checkers', [
                     dict([('checker', checker),
                           ('solution',
                            checker_solution(
                                checker, '%s/%s' %
                                (si(solver, instance), checker))),
                           ('verified',
                            solution('%s/%s/lrat-check.out' %
                                     (si(solver, instance), checker))),
                           ('stats',
                            checker_stats(
                                checker, '%s/%s/' %
                                (si(solver, instance), checker)))] +
                          runlim('%s/%s/runlim.out' %
                                 (si(solver, instance), checker)))
                     for checker in checkers
                 ])]) for solver in solvers
        ]
    } for instance in instances]
    for instance in data:
        for solver in instance['solvers']:
            for checker in solver['checkers']:
                checker['result'] = summarize_checker_result(checker)
    return data


def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    json.dump(results(), sys.stdout)


if __name__ == '__main__':
    main()
