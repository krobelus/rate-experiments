#!/usr/bin/env python3

from plot import (pretty_name, global_data, dst, checkers, solvers, instances,
                  time, space, checked_by_all_4, verified_by_all_4,
                  verified_by, checked_by)
import os
import sys
import csv
from sys import exit
from results import dimensions

os.chdir(os.path.dirname(os.path.abspath(__file__)))


# def q(s): return f'~{s}~'
def q(s): return s


def extract(cols, row):
    return [row[col] for col in cols]


def pretty_column_title(col):
    if '-' not in col:
        return col
    for checker in checkers:
        if col.startswith(checker):
            return pretty_name(checker) + ' ' + col[len(checker) + 1:]
    return col


def csv_header(writer, cols):
    writer.writerow([pretty_column_title(col) for col in cols])


def summary():
    num_proofs = len(solvers) * len(instances)
    generated_proofs = [row for row in global_data if row['sresult'] != 'n/a']
    ratio_generated_proofs = len(generated_proofs) / num_proofs

    checked_proofs = [row for row in generated_proofs if checked_by_all_4(row)]
    ratio_checked_proofs = len(checked_proofs) / num_proofs
    verified_proofs = [row for row in checked_proofs if verified_by_all_4(row)]
    ratio_verified_proofs = len(verified_proofs) / num_proofs

    cs = (q(pretty_name(checker)) for checker in checkers)

    with open(f'{dst}/summary.csv', 'w') as summary:
        print(
            f'''
    Number of checkers,   {len(checkers)} ({' + '.join(cs)})
    Number of solvers,    {len(solvers)}
    Number of instances,  {len(instances)}
    Number of proofs,     {len(solvers)} * {len(instances)} = {num_proofs}
    Generated proofs,     {len(generated_proofs)} / {num_proofs} ({"%.2f" % (ratio_generated_proofs * 100)}%)
    Proofs processed by all checkers,       {len(checked_proofs)} / {num_proofs} ({"%.2f" % (ratio_checked_proofs * 100)}%)
    Proofs verified by all checkers,       {len(verified_proofs)} / {num_proofs} ({"%.2f" % (ratio_verified_proofs * 100)}%)
    '''.strip(),
            file=summary)


def table_performance():
    data = [row for row in global_data if verified_by_all_4(row)]
    with open(f'{dst}/performance.csv', 'w') as f:
        writer = csv.writer(f)
        csv_header(writer, ['instance', 'solver'] + time + space)
        for row in data:
            writer.writerow(
                [q(row['instance']), q(row['solver'])] + extract(time, row) +
                extract(space, row))


def table_difference_accepted():
    data = [row for row in global_data if verified_by(('rate', 'rate-d'))(row)]
    data.sort(key=lambda row: -
              (float(row['rate-time']) -
               float(row['rate-d-time'])))
    with open(f'{dst}/difference-accepted.csv', 'w') as f:
        writer = csv.writer(f)
        csv_header(writer, [
            'instance', 'solver', 'rate-reason-deletions', 'rate-time',
            'rate-d-time'
        ])
        for row in data:
            writer.writerow(
                [q(row['instance']), q(row['solver'])] + extract((
                    'rate-reason-deletions', 'rate-time', 'rate-d-time'), row))


def table_difference():
    data = [row for row in global_data if checked_by(('rate', 'rate-d'))(row)]
    with open(f'{dst}/difference.csv', 'w') as f:
        writer = csv.writer(f)
        csv_header(writer, [
            'instance', 'solver', 'rate-result', 'rate-d-result',
            'rate-reason-deletions', 'rate-time', 'rate-d-time'
        ])
        for row in data:
            writer.writerow(
                [q(row['instance']), q(row['solver'])] + extract(
                    ('rate-result', 'rate-d-result', 'rate-reason-deletions',
                     'rate-time', 'rate-d-time'), row))


def tmp():
    data = [
        row for row in global_data
        if checked_by(('rate-d',
                       'drat-trim'))(row)
                       and float(row['rate-d-time']) < 20
                       and float(row['rate-d-time']) < float(row['drat-trim-time'])
    ]
    # highest space difference first
    data.sort(key=lambda row: (float(row['drat-trim-space']) - float(row[
        'rate-d-space'])))
    # for row in data[:10]:
    for row in data[:]:
        print('%50s %50s %10s ' % (row['instance'], row['solver'], row['stime']), end='')
        # print(f"{row['instance']}\t{row['solver']}", end=' ')
        for checker in 'rate-d', 'drat-trim':
            print('%10s %10ss %10s MB ' % (
            checker,
            row[f'{checker}-time'],
            row[f'{checker}-space']
            ), end='')
            # print(
            #     f"{checker}: {row[f'{checker}-time']} s {row[f'{checker}-space']} MB",
            #     end=' ')
        print()
    exit(0)


if __name__ == '__main__':
    # tmp()
    summary()
    table_performance()
    table_difference()
    table_difference_accepted()
