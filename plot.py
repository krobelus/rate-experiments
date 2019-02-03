#!/usr/bin/env python3

import os
import sys
import csv
import matplotlib.pyplot as plt

from results import dimensions

os.chdir(os.path.dirname(os.path.abspath(__file__)))

dst = sys.argv[1]
if not os.path.isdir(dst):
    assert not os.mkdir(dst)

checkers, solvers, instances = dimensions()
time = [f'{checker}-time' for checker in checkers]
space = [f'{checker}-space' for checker in checkers]

global_data = [row for row in csv.DictReader(sys.stdin)]


def _col(data, name, conversion=lambda x: x):
    return [conversion(row[name]) for row in data]


def col(data, name):
    return _col(data, name, lambda s: -1 if s == '' else float(s))


def filename(tag, ys):
    ident = '+'.join(ys)
    return f'{dst}/{tag}_{ident}.png'


def plot(fun):
    def wrapper(
            uid,
            ys,
            *,
            funnel=None,
            sorting=None,
            xlabel=None,
            ylabel=None,
            legend=True,
            **kwargs):
        if funnel is None:
            data = None
        else:
            data = [row for row in global_data if funnel(row)]
            if not data:
                return
        if sorting is not None:
            data.sort(key=sorting)
        filename = f'{dst}/{uid}.png'
        assert not os.path.exists(
            filename), f"plot '{filename}' already exists"
        fun(data, ys, **kwargs)
        if legend:
            plt.legend()
        if xlabel is not None:
            plt.xlabel(xlabel)
        if ylabel is not None:
            plt.ylabel(ylabel)
        plt.savefig(filename)
        plt.close()
    return wrapper


@plot
def barplot(data, ys, *, plotfun=plt.plot, order_by=None):
    width = 1.0

    def offset(o):
        stride = (len(ys) + 0.5)
        return [o + stride * i for i in range(len(data))]
    bar = 0
    for y in ys:
        plt.bar(offset(bar), col(data, y), width,
                color=color(y), label=label(y))
        bar += 1


@plot
def cactus(data, ys):
    x = list(range(len(data)))
    for y in ys:
        plt.scatter(x, sorted(col(data, y)), s=2, c=color(y),
                    marker=marker(y), label=label(y))


@plot
def correlation(data, ys, *, labels=None, ylabels=None, markers=('_', '|')):
    x = list(range(len(data)))
    fig, ax1 = plt.subplots()
    ax2 = ax1.twinx()
    ax1.set_ylabel(ylabels[0])
    ax2.set_ylabel(ylabels[1])
    lines = []
    for (y, label, ax, marker) in zip(ys, labels, [ax1, ax2], markers):
        lines += [ax.scatter(x, col(data, y), s=10,
                             color=color(y), marker=marker, label=label)]
    ax1.legend(lines, (l.get_label() for l in lines), loc='upper left')


@plot
def fixed_bars(_data, ys, *, magnitudes=None):
    width = 0.75
    bar = 0
    plt.axes().get_xaxis().set_ticks([])
    for i in range(len(magnitudes)):
        y = ys[i]
        magnitude = magnitudes[i]
        plt.bar(bar, magnitude, width, color=color(y), label=label(y))
        bar += 1


COLOR = {
    'rate-old': 'C5',
    'rate-d': 'C4',
    'rate': 'C0',
    'gratgen': 'C3',
    'drat-trim': 'C1',
    'stime': 'C2',
    'overhead': 'C7',
}


def color(col):
    if col == 'stime':
        return 'C2'
    if 'reason-deletions' in col:
        return 'C6'
    for key in COLOR:
        # if col.startswith(f'{key}-'):
        if col.startswith(key):
            return COLOR[key]
    assert False, f"don't know how to color column: '{col}'"


MARKER = {
    'rate-d': '|',
    'rate': '_',
    'gratgen': 'v',
    'drat-trim': '^',
}


def marker(col):
    for key in MARKER:
        if col.startswith(f'{key}-'):
            return MARKER[key]
    assert False, f"no marker for column: '{col}'"


def pretty_name(name, org=False):
    if name == 'rate-d':
        name = 'rate --skip-unit-deletions'
    return f'~{name}~' if org else name


def label(col):
    if col == 'overhead':
        return 'runtime'
    if col == 'stime':
        return 'solver runtime'
    if col.endswith('-time'):
        dash = len(col) - len('-time')
        return pretty_name(col[:dash])
    if col.endswith('-space'):
        dash = len(col) - len('-space')
        return pretty_name(col[:dash])
    if col in ('rate', 'rate-d'):
        return pretty_name(col)
    if col.endswith('-reason-deletions'):
        return 'number of reason deletions'
    assert False, f"don't know how to label column: '{col}'"


def checked_by(checkers):
    checkers = set(checkers)

    def predicate(row):
        return all(row.get(f'{checker}-result') !=
                   'n/a' for checker in checkers)
    return predicate


def checked_by_all_4(row):
    return checked_by(('rate', 'rate-d', 'gratgen', 'drat-trim'))(row)


def verified_by(checkers):
    checkers = set(checkers)

    def predicate(row):
        # return all(row.get(f'{checker}-solution') in ('VERIFIED', 'ACCEPTED')
        # for checker in checkers)
        return all(row.get(f'{checker}-result') ==
                   'verified' for checker in checkers)
    return predicate


def verified_by_all_4(row):
    'instances verified by all checkers'
    return verified_by(('rate', 'rate-d', 'gratgen', 'drat-trim'))(row)


def verified_by_rate_rate_d_reason_dels_above(i):
    def verified_by_rate_rate_d(row):
        'instances verified by rate and rate --skip-unit-deletsion'
        return (verified_by(('rate', 'rate-d'))(row)
                and (float(row['rate-time']) - float(row['rate-d-time'])) > i)
    return verified_by_rate_rate_d


def verified_by_all_4_above_500s(row):
    '''instances verified by all checkers where rate took more than 500s'''
    try:
        return float(row.get('rate-time')) >= 500 and verified_by_all_4(row)
    except BaseException:
        return False


def ylabel(feature):
    if feature[0].endswith('-time'):
        return 'runtime (s)'
    if feature[0].endswith('-space'):
        return 'memory usage (MB)'
    assert False, f"don't know how to label y for {feature[0]}"


def plot_discrepancy():
    data = [row for row in global_data if checked_by(('rate', 'rate-d'))(row)]
    accepted_by_rate = len(
        [row for row in data if row['rate-result'] == 'verified'])
    accepted_by_rate_d = len(
        [row for row in data if row['rate-d-result'] == 'verified'])
#    with open('t/accepted-by-rate', 'w') as f:
#        f.write(accepted_by_rate)
#    with open('t/accepted-by-rate-d', 'w') as f:
#        f.write(accepted_by_rate_d)
    fixed_bars(
        'discrepancy',
        ('rate',
         'rate-d'),
        magnitudes=(
            accepted_by_rate,
            accepted_by_rate_d),
        ylabel='number of accepted proofs')


def plot_correlation_reason_deletions_overhead():
    uid = 0
    for baseline in 'rate-d', 'drat-trim':
        for minimum_overhead in 0, 300:
            for row in global_data:
                try:
                    tmp = float(row['rate-time']) - \
                        float(row[f'{baseline}-time'])
                    row['overhead'] = tmp
                except BaseException:
                    pass
            feature = ['overhead', 'rate-reason-deletions']
            labels = [
                'overhead of handling deletions',
                'number of deleted reason clauses']
            ylabels = ('overhead (s)', 'deleted reason clauses')
            funnel = verified_by_rate_rate_d_reason_dels_above(
                minimum_overhead)

            def sorting(row): return row['overhead']
            correlation(
                f'correlation-{uid}',
                feature,
                funnel=funnel,
                sorting=sorting,
                xlabel=funnel.__doc__,
                labels=labels,
                ylabels=ylabels,
                legend=False)
            uid += 1


def plot_performance():
    uid = 0
    for plottype in barplot, cactus:
        for funnel in verified_by_all_4, verified_by_all_4_above_500s:
            for feature in time, space:
                plottype(
                    f'performance-{uid}',
                    feature,
                    funnel=funnel,
                    ylabel=ylabel(feature),
                    xlabel=funnel.__doc__)
                uid += 1


if __name__ == '__main__':
    plot_correlation_reason_deletions_overhead()
    plot_discrepancy()
    plot_performance()
