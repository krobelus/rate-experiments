---
title: Implementation of Complete and Efficient DRAT Proof Checking
author: Johannes Altmanninger
bibliography: references.bib
csl: ieee.csl
---

::: {.abstract}
**Abstract:**
The clausal proof format DRAT is the de facto standard way to certify SAT
solvers' unsatisfiability results.  State-of-the-art DRAT checkers ignore
deletions of unit clauses, which means that they are checking against a
proof system that differs from the specification of DRAT.  We demonstrate
that it is possible to implement a competitive checker that honors unit
deletions at small amortized costs.  Many SAT solvers produce proofs that
are incorrect under the DRAT specification, because they contain spurious
unit deletions. We present patches for competitive SAT solvers to produce
correct proofs with respect to the specification.
:::

1. Introduction
===============

In past decades, there has been significant progress in the area of SAT solver
technology. As a result of the high complexity of SAT solvers, they have
had documented bugs [@BrummayerBiere-SMT09; @BrummayerLonsingBiere-SAT10].
To protect against these, there are checkers that verifiy a solver's
result. The result *satisfiable* is given with a model which is trivial
to validate in linear time.  The converse result, *unsatisfiable*, can be
certified with a proof of unsatisfiability given by the solver. A proof
checker, a program independent of the solver, can verify such proofs.

In SAT competitions, solvers are required to produce proofs in the DRAT
format, A DRAT proof is a sequence of lemmas (clause introductions) and clause
deletions.  One problem with such proofs is that they can grow very large.
In order to counteract this, the format is already as space-efficient as
possible, at the cost of proof checking runtime. A measure that was taken
to decrease checking time was the includion of deletion information in
proofs[@Heule_2013]. Nevertheless, checking a proof can still take a similar
amount to solving the formula.

Some solvers produce proofs containing some deletions of clauses even though
the solver operates as though these clauses were not deleted.  To accomodate
for this, state-of-the-art proof checkers ignore deletion instructions that
might be one of them.  Consequently, the checkers are not faithful to the
specification of DRAT proofs [@rebola2018two].

We refer to the original definition of the proof format as *specified* DRAT
and to the one that is actually implemented by state-of-the-art checkers
as *operational* DRAT [@rebola2018two]. Merely checking operational DRAT is
sufficient for current use cases, provided the solver produces a proof that
coincides with what it does internally, however, checking specified DRAT
can be required for verifying inprocessing steps that use unit deletions
[@rebola2018two].

Checking specified DRAT is quite a bit more complicated but there exists an
efficient algorithm [@RebolaCruz2018].  Previous empirical results suggest
that the class of proofs that today's solvers produce can be verified with a
checker of either flavor exhibiting roughly the same time and memory usage. We
provide more detailed results, showing that on average this is true and that
a high number of unit deletions tends to increase (and sometimes decrease)
checking costs for specified DRAT compared operational DRAT.

To show the incorrectness of a proof, it suffices show that a single lemma in
the proof cannot be inferred.  We use a modified version of the previously
unpublished SICK incorrectness certificate format to give information on
why a lemma cannot be derived.  This certificate can be used to verify the
incorrectness of the proof efficiently and help developers find bugs in
proof generation procedures.

To sum up, there are three distinct contributions in this work:

1. We indicate why checkers ignore certain deletions and provide patches
for solvers to make them generate proofs without spurious deletions, that
are therefore correct under either flavor of DRAT.

2. Our extension to the SICK certificate format is introduced.

3. We present the implementation of our checker for specified DRAT
that includes the most important optimizations present in other checkers.
This allows us to provide empirical evidence that checking specified DRAT
is, on average, as expensive as operational DRAT, albeit more complicated.

The rest of this paper is organized as follows: In [the following
section][2. Preliminaries] we will introduce preliminary knowledge about SAT
solving, proofs of unsatisfiability, proof checking techniques, the problem
with the ignored deletions and existing checkers.  After establishing novel
terminology in [the following section][3. Redundant Reason Deletions], our
first contribution, proposal on how to change solvers to produce unambiguously
correct proofs, can be found in [Section 4][4. Solvers].  The SICK format along
our extension will be described in [Section 5][5. SICK Format].  The third
contribution will be discussed in [Section 6][6. Checker Implementation] with
experimental results being presented in [the following section][7. Experimental
Evaluation].  Finally, we draw a [conclusion][8. Conclusion] and give outlook
on [future work][9. Future Work] in the area of proof checking.

2. Preliminaries
================

Notation
--------

A literal is a propositional variable, like $x$, or a negation of a variable,
denoted by $\overline{x}$. A clause is a disjunction of literals and is
denoted by juxtaposition of the disjuncts, e.g. we write $xy\overline{z}$
for $x \lor y \lor \overline{z}$.

An assignment is a set of literals. All literals in an assignment are
considered to be satisified by that assignment.  Conversely, the negations
of those literals are falsified by that assignment.  Other literals are
unassigned.  If there are some unassigned literals, then the assignment
is partial.  If an assignment contains a literal in both polarities,
this is a conflict, i.e., the assignment is inconsistent.

SAT Solving
-----------

SAT solvers work on formulas in conjunctive normal form (CNF), conjunctions
of clauses.  A clause is satisfied by an assignment $I$ if any one literal in
the clause is satisfied by $I$.  A CNF formula is satisified by $I$ if each
of its clauses is satisfied by $I$.  An assignment that satisfies a formula
is called a model for that formula.

A formula is satisfiable if there exists a model for it.  A SAT solver takes
as input a formula and finds a single model if the formula is satisfiable.
Otherwise, the solver can provide a proof that the formula is unsatisfiable.

While searching for a model, a solver builds up a (partial) assignment and
records a order in which the literals where assigned and *reason clause*
for each assigned literal.  We call this data structure the trail.

DPLL-style SAT solvers search through the space all possible assignments.
They make assumptions, adding literals to the trail that might be part of
a satisfying assignment.  The search space is greatly reduced by formula
simplification, such as unit propagation which will be introduced in the
next subsection.  Such simplifications prune assignments that are definitely
unsatisfiable, by adding literals to the trail. These literals are said to
be forced, because they, unlike assumptions, are necessarily satisfied in
any model that extends the current trail.  If simplifications are done on a
trail without any assumptions, the assignment is the set of top-level forced
literals, the set of literals that are part of any model.  These are essential
for a checker as we will see later.

Most modern SAT solvers implement Conflict Driven Clause Learning (CDCL) where
they learn clauses based on conflicts stemming from assumptions that render
the formula unsatisfiable.
These clauses are added to the formula until a top-level conflict (without
any assumptions) is derived eventually if the formula is unsatisfiable.
Clauses that are not used to derive conflicts are deleted regularly to avoid
a slowdown in unit propagation.

Unit Propagation
----------------

A *unit clause* has only falsified literals except for its single non-falsified
*unit literal*.

If a formula contains a unit clause, any model must contain the unit literal.
Then a solver can perform unit propagation add the unit to the trail, discard
any clause containing it (because they will be satisfied by the unit),
and remove any of its negations from the remaining clauses.  The last step
may induce new unit clauses and thus trigger further propagation. A conflict
arises as soon as two literals of opposing polarity are assigned which shows
that the formula is unsatisfiable. A solver (or checker) records the clause that
was unit for each literal in the trail as the *reason* for that literal.

The two-watched-literal scheme [@Moskewicz:2001:CEE:378239.379017] is used
to keep track of which clauses can trigger propagation . It consists of a
watchlist for each literal, which is an sequence of clause references. All the
clauses in the watchlist of some literal said to be *watched by* that literal.
As the name indicates, each clause is watched by two literals, these are
also called the *watches*.  To check if a clause is unit, it suffices to
look at the watches given Invariant 1 from [@RebolaCruz2018] is maintained.

**Invariant 1.** If a clause is watched on literals $l$ and $k$, and the
current trail $I$ falsifies $l$, then $I$ satisfies $k$.

Note that, as in [@RebolaCruz2018], clauses of size one are extended by a
single literal $\overline{\top}$ to make the manipulations of watches work
the same way for all clauses.

Clausal Proofs
--------------

A formula in CNF is modeled as a multiset of clauses.  Each step in a
clausal proof adds a clause to the current formula, or deletes one from it.
A solver or checker maintains a a trail of literals that are forced by
unit propagating in the accumulated formula.  The straightforward way to
reproduce a proof of unsatisfiability is to perform proof steps, until the
trail contains a conflict, which means that a top-level conflict was found.

Redundancy Properties
---------------------

A clause is redundant according to some criteria in Formula $F$ if it can
be derived from the formula by a proof system associated with that criteria.

A clause $C$ is RUP (reverse unit propagation) in formula $F$ if unit
propagation in $F \cup \{ \{\overline{l}\} \,|\, l \in C \}$ leads to
a conflict.

A clause $C$ is a *resolution asymmetric tautologies* (RAT)
[@inprocessingrules] on some literal $l \in C$ with respect to formula $F$
whenever for all clauses $D \in F$ where $\overline{l} \in D$, the resolvent
$C \cup (D \setminus \{\overline{l}\})$ is RUP in $F$. We call $D$ the
resolution candidate.

Deletions
---------

Resolution refutations are exponential in the size of the formula, as are DRAT
proofs. To substantially reduce checking efforts, clause deletion information
has been added to proof formats [@Heule_2014].  Clauses that are subsumed
by some other clause can be safely deleted without losing information.

DRAT Proofs
-----------

Proof based on RUP alone are not expressive enough to cover all inprocessing
techniques in modern SAT solvers. For this reason, more powerful
property RAT is used today[@rat]. Clause deletion was introduced to make
checking more efficient[@Wetzler_2014].

A DRAT (*delete resolution asymmetric tautology*) proof is a clausal proof
with deletions where every lemma is RAT.  Given that a solver emits all
learned clauses and clause deletions in the DRAT proof, the checker can
reproduce the exact same formula that the solver was working on.

LRAT Proofs
-----------

The runtime and memory usage of DRAT checkers can exceed the ones of the
solver that produced the proof. The resulting need to have a DRAT checker be as
efficient as possible makes it difficult to implement a mechanically verified
checker. This is remedied by making the DRAT checker output an optimized (=
small) and annotated proof in LRAT format [@cruz2017efficient]. Checking this
proof does not require blind propagation and there are verified implementations
available[^acl2].

An LRAT proof is a clausal proof just like DRAT, but it includes clause hints
for resolution candidates and all unit clauses that are necessary to derive
a conflict to show that the resolvent is a RUP.

Backwards Checking
------------------

While searching, SAT solvers can not know, which learned clauses are useful
in a proof, so they simply add all of them as lemmas. This means that many
lemmas may not be necessary in a refutation.

To avoid checking useless lemmas, the proof is checked backwards, starting
from the empty clause, and only lemmas that are reasons for the conflict
are checked [@Heule_2013].

This requires two passes: a forward pass performing incremental prepropagation
[@RebolaCruz2018] until the conflict clause is found, and a backward pass
that actually checks each clause introduction.

Doing this, a proof checker computes an unsatisfiable core, consisting of
all checked lemmas plus the clauses in the original formula that were
used to derive a conflict and thus make an inference at any point.


Core-first Unit Propagation
---------------------------

In order to keep the core small and reduce checking costs, core-first unit
propagation was introduced [@Heule_2013].  It works by doing unit
propagation in two phases:

1. Propagate exhaustively using all clauses that are already known to be in
the core.
2. Consider non-core clauses: propagate only the first unit found and go
to 1.  If there is no unit found, the propagation has reached its fixed-point
without a conflict.

Which results in a local minimum of clauses being added to the conflict graph,
and subsequently the core. Non-core lemmas do not have to be checked.

Reason Deletions
----------------

As explained in [@RebolaCruz2018] when checking a proof without deletions
of reason clauses, the trail grows monotonically, that is, it never shrinks
at any proof step during the forward phase. Therefore, during the backwards
phase, it is trivial to undo the propagations done after a lemma introduction
by merely truncating the stack.

However, when there are reason deletions it is not as simple.  During the
forward pass, when a reason clause is deleted its associated unit is
unassigned.  If this unit was necessary to propagate some other unit, this
may be unassigned as well, and so on. All these literals form the cone of
influence (see [@RebolaCruz2018]) of the first unit and are recorded in the
checker, alongside their positions in the trail, and reasons clauses.

The recorded information can then be used in the backward pass to patch
the trail at any step that is a reason deletion, in order for the trail to
be exactly as it was during the forward phase. The tricky part here is to
correctly restore the watch invariant in all affected clauses.

When a reason deletion is processed during the backwards phase, each literal in
the cone will be reintroduced into the trail at the recorded position. This is
fairly straightforward.  Consider literal $l$ in the cone. Before applying
the backwards deletion it could have been satisfied or unassigned (but not
falsified).  After reintroducing it, it is assigned. Therefore, a clause
containing $\overline{l}$ might become unit without the checker noticing.
Because of this, the watchlists of all reverse cone literals $\overline{l}$
have to be traversed to restore the watch invariant.
Each of those clause is watched on falsified literal $\overline{l}$, which
needs to be replaced by a non-falsified literal.
Possibly, both watches are falsified by the reintroductions, in that case
both will be replaced by non-falsified literals.

However, if the clause has only one non-falsified literal (it is necessarily
satisifed because of invariant 1), then the other watch must be the most
recently falsified literal [@RebolaCruz2018; Example 5]. Let us illustrate
the reason for this by means of an example. Imagine clause $xyz$ with $I =
\{x, \overline{y}, \overline{z}\}$.  It is watched on the first two literals,
$x$ and $y$.  A clause introduction step is processed backwards which causes
$x$ and $\overline{z}$ to be unassigned, e.g. $I' = \{\overline{y}\}$ but the
watches are not touched, hence Invariant 1 is violated.  In particular, during
a RUP check, $\overline{z}$ could be assigned, making the clause unit which
would go unnoticed, because $z$ is not watched.  To avoid such a situation,
after performing a deletion instruction backwards, such a falsified watch must
be set to the most recently falsified literal.  This ensures that, during any
backwards introduction, if the satisfied watch (here $x$) is being unassigned,
the other watch will also be unassigned, thus restoring invariant 1.

Existing Checkers
-----------------

Previous work has yielded checkers which we draw upon heavily. In fact,
our current implementation contains almost no novelties but merely combines
the ideas present in existing checkers.

`DRAT-trim`
-----------

The seminal reference implementation; Marijn Heule's `DRAT-trim` can produce an
optimized proof in LRAT format. We use their way of producing LRAT proofs and
make sure that all our proofs are accepted by the verified checker [^acl2].
This gives us confidence in the correctness of our implementation and allows
for a comparison of our checker with `DRAT-trim` since they do roughly the
same thing except for the unit deletions.

GRAT Toolchain
--------------

More recently, Peter Lammich has published the GRAT toolchain
[@lammich2017grat] that is able to outperform `DRAT-trim`
[@lammich2017efficient].

They first produce a GRAT certificate which is (similar to LRAT) with the
`gratgen` tool, after which formally verified `gratchk` can be used to
check the certificate, guaranteeing that the original formula is indeed
unsatisfiable.

They introduce some optimizations:

- Separate watchlists for core and non-core clauses. This speeds up unit
propagation, so we use it in our implementation.

- Resolution candidate caching / RAT run heuristic [@lammich2017efficient]:
DRAT proofs tend to contain sequences of RAT lemmas with the same pivot,
in which case they only compute the list of RAT candidates once per sequence
and reuse it for all lemmas with the same pivot. We did not implement that
because the number of RAT introductions in our benchmarks is negligible when
compared to the number of RUP introductions.

We also implement GRAT generation in our tool which. However, it seems that
the `gratchk` tool is not designed to handle unit deletions (apparently they
are ignored) so it will fail to handle our GRAT certificates for proofs with
unit deletions.

`rupee` [^rupee]
----------------

This is the original implementation of the algorithm to handle reason
deletions. We use exactly the same algorithm.  During our research we
found an issue in the implementation which was fixed [^fix-revise-watches].

Previously, `rupee` appears to be an order of magnitude slower than
`DRAT-trim` [@RebolaCruz2018].  However, we believe that this overhead
is primarily not a consequence of the algorithmic differences but exists
mostly due to differences in the parsing implementation [^rupee-parsing]
and other implementation details.

[^rupee-parsing]: Both `rupee` and `DRAT-trim` use a fixed-size hash table
to locate deleted clauses but `rupee`'s is smaller by one order of magnitude,
which may explain most of the difference in performance.

Additionally `rupee` does not use core-first unit propagation while the
other checkers do. This is important for swift checking on some instances.

3. Redundant Reason Deletions
=============================

Deleting a reason clause generally shrinks the trail.  However, if, and only
if there is another clause that can act as reason for the same literal at
some point during unit propagation, then the set of literals in the trail
does not change.  We call this special case a *redundant reason deletion*,
and the other case a *non-redundant reason deletion* Note that the term *unit
deletion* comprises deletions of any unit clause, that is, reason deletions
and other deleted units that were not propagating.

An simple example for a redundant reason deletion would be the deletion of
a size-one clause that occurs twice in the formula.

A proof of unsatisfiability generated by a SAT solver should not contain
any non-redundant reason deletions.  Other current checkers can report unit
deletions and reason deletions but they do not distuingish between redundant
and non-redundant reason deletions.  Our tool also outputs the number of
non-redundant reason deletions [^reason-deletions-shrinking-trail]. This
might be useful to sanity-check SAT solvers' proof generation procedures.

Given a proof without non-redunant reason deletions, checkers for *operational*
and *specified* DRAT behave exactly the same way.

[^reason-deletions-shrinking-trail]: The are called `reason deletions
shrinking trail` in the output of `rate`.

4. Solvers
==========

In this section we take a look at why the discrepant proofs are produced in
the first place, and present patches to make solvers generate proofs without
any ambiguitiy about how to check them.

As stated already in [@RebolaCruz2018], most solvers at competitions emit
proofs with (non-redundant) reason deletions.  The overwhelming majority of
solvers submitted to the main track of the 2018 SAT competition is based on
`MiniSat` or `CryptoMiniSat`.  Only their proofs contain non-redundant reason
deletions. We explain here why this is the case.

Used during the simplification phase, the method `Solver::removeSatisfied`
takes a collection of clause references. Each of those clauses that is
satisfied, is removed from the clause database and added as deletion to
the DRAT proof output.  Note that it is only called at decision level zero,
which means that those clauses will be satisfied indefinitely for the rest
of the solving time.

In `MiniSat`, *locked* clauses are reasons for some literal in the trail.
Currently, `Solver::removeSatisfied` also deletes locked clauses, however,
the (transitively) induced assignments are not undone.  This suggests that a
locked clause is implicitly kept in the formula, even though it is deleted.
To match this solver's behavior, current DRAT checkers ignore deletions of
unit clauses, which includes all reason clauses, which means they do not
undo any assignments when deleting clauses.

There are two obvious possible changes to `MiniSat` to produce proofs that
do not require this workaround of ignoring unit deletions when checking.

1. Do not remove locked clauses during simplification.

2. Before to removing locked clauses, emit the corresponding propagated literal
as addition in the DRAT proof.
Suggested by Mate Soos[^suggestion-add-units], this option is also the
preferred one to two other solver authors[^mergesat-pr] [^varisat-pr].
Additionally, this is implemented in `CaDiCaL`[^cadical] for initial
simplification of the formula.

We provide patches implementing these for `MiniSat` version 2.2
(1.  [^patch-MiniSat-keep-locked-clauses] and 2.[^patch-MiniSat]),
and the winner of the main track of the 2018 SAT competition
(1.[^patch-MapleLCMDistChronoBT-keep-locked-clauses] and
2.[^patch-MapleLCMDistChronoBT]).

The same methods can be applied easily to other `MiniSat`-based solvers.
As it is very small, the patch implementing the second variant for `MiniSat`
is displayed below.

```diff
From 15d7560d6c340a4e8d93cb7469fe976cc43690da Mon Sep 17 00:00:00 2001
From: Johannes Altmanninger <aclopte@gmail.com>
Date: Tue, 28 May 2019 14:19:14 +0200
Subject: [PATCH] emit unit in DRAT proof before deleting locked clauses

---
 minisat/core/Solver.cc | 8 ++++++--
 1 file changed, 6 insertions(+), 2 deletions(-)

diff --git a/minisat/core/Solver.cc b/minisat/core/Solver.cc
index ddc3801..5941449 100644
--- a/minisat/core/Solver.cc
+++ b/minisat/core/Solver.cc
@@ -632,9 +632,13 @@ void Solver::removeSatisfied(vec<CRef>& cs)
     int i, j;
     for (i = j = 0; i < cs.size(); i++){
         Clause& c = ca[cs[i]];
-        if (satisfied(c))
+        if (satisfied(c)) {
+            if (output != NULL && locked(c)) {
+                Lit unit = c[0];
+                fprintf(output, "%i 0\n", (var(unit) + 1) * (-2 * sign(unit) + 1));
+            }
             removeClause(cs[i]);
-        else{
+        } else{
             // Trim clause:
             assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
             for (int k = 2; k < c.size(); k++)
```

5. SICK Format
==============

When a proof is found to be incorrect, our tool outputs an incorrectness
certificate in our modified SICK format. This certificate can be used by
our tool `sick-check` to verify the incorrectness of the proof without doing
any unit propagation.

Example
-------

Here is an example of a SICK certificate in TOML[^toml] syntax, stating that
a RAT check failed on all three possible pivots.

```toml
# Failed to prove lemma -768 -769 917 0
proof_format   = "DRAT-arbitrary-pivot"
proof_step     = 22452 # Failed line in the proof
natural_model  = [2088, -692, -696, 673, 713, -416, 1940, 1960, 1932, 708,
		  -702, 1039, -1964, -1967, 1938, 1937, -1828, 1975, -1985,
		  1952, -437, -1936, -1977, 1833, -407, -1496, -1848, -1855,
		  1131, -434, 1135, 1933, 1010, 1888, -1150, -1309, -1154,
		  768, 769, -917, -1152, ]
[[witness]]
failing_clause = [-765, 768, 743, ]
failing_model  = [765, -743, ]
pivot          = -768
[[witness]]
failing_clause = [769, -1565, -824, ]
failing_model  = [1565, 824, 1900, ]
pivot          = -769
[[witness]]
failing_clause = [-917, 884, -891, ]
failing_model  = [-884, 891, ]
pivot          = 917
```

Grammar
-------

```
SICK := Intro Witness*
Intro := ProofFormat ProofStep NaturalModel
ProofFormat := 'proof_format' '='
		( "DRAT-arbitrary-pivot"
		| "DRAT-pivot-is-first-literal"
		)
ProofStep := 'proof_step' '=' Integer
NaturalModel := 'natural_model' '=' ListOfLiterals
Witness := FailingClause FailingModel [ Pivot ]
FailingClause := 'failing_clause' '=' ListOfLiterals
FailingModel := 'failing_model' '=' ListOfLiterals
Pivot := 'pivot' '=' Literal
```

Explanation
-----------

- `proof_format` describes the proof format to use.
   - `DRAT-arbitrary-pivot`: DRAT checking where the pivot can any literal in
   the lemma. This requires one witness (counter example) for each possible
   pivot in the failing lemma. The pivot has to be specified for each witness.
   - `DRAT-pivot-is-first-literal`: Similar, but there is only one witness.
   The pivot needs to be the first literal in the lemma.
- `proof_step` specifies the proof step that failed, starting at one.
  In case of a textual proof this corresponds to the line number of the
  introduction instruction that failed.
- `natural_model` gives the partial model or trail before
  checking this proof step, obtained by exhaustively propagating units
  in the accumulated formula. This is included to avoid having to perform
  propagation in a checking tool.

Each witness is a counterexample to some redundancy check.

- `failing-clause`: A clause in the formula. For RAT variants this is the
  resolution candidate where RUP failed to produce a conflict.
- `failing-model`: The literals that were added to the natural model (trail)
  when performing the redundancy check. When checking for RAT this is the
  set of literals that are propagated along the reverse resolvent.
- `pivot`: This specifies the pivot that was used for this witness.

Note that if the failed lemma is the empty clause, no witness is needed.

Semantics
---------

Our tool `sick-check` accepts SICK certificates that fulfil below properties.

Let $m_n$ be the natural model.

1. The proof contains the proof step.
2. $m_n$ is consistent.
3. $m_n$ contains the reverse units from the failing lemma.
4. The accumulated formula up to and excluding the failing lemma contains
no clause that is unit under $m_n$ and is not already in $m_n$.
5. For format "DRAT-arbitrary-pivot", all pivots are specified and precisely
match the literals in the failing lemma.
6. For each witness, let the $m_f$ be the union of natural model and failing model.
    1. The failing clause is in the formula.
    2. $m_f$ is consistent.
    3. $m_f$ contains the reverse units from the resolvent of the .
    4. $m_f$ contains no clause that is unit under $m_f$ and not already in $m_f$.

Contribution
------------

Our contribution consists of adding support for proof format
`DRAT-arbitrary-pivot` which requires multiple witnesses, and the usage
of TOML[^toml].

6. Checker Implementation
=========================

The implementation (`rate`) is available [^rate].

Features
--------

- output core lemmas as DIMACS or LRAT for accepted proofs
- output certificate of unsatisfiability for rejected proofs, see [SICK format]
- competitive performance due to backwards checking with core-first unit
propagation
- option to ignore unit deletions (flag `-d` or `--skip-unit-deletions`)
- decompress input files (Gzip, Zstandard, Bzip2, XZ, LZ4)
- The debug build comes with lots of assertions, including checks for
arithmetic overflows and lossy narrowing conversions.

We initially reserved 62 bits to identify clauses while `DRAT-trim` uses 30.
Unfortunately, this caused excess memory consumption because we need to encode
clause hints in the LRAT proof which is much larger than the input proof and
needs to be kept in memory until the proof checking is complete. Future proof
formats should allow checking without keeping the entire proof in memory,
although backwards checking might make this difficult.  In order to make
`rate` comparable to `DRAT-trim` in terms of memory consumption, we also
use 30 bits for clause hints in the LRAT output.

7. Experimental Evaluation
==========================

To evaluate our tool, we performed experiments on proofs produced by
solvers from the SAT competition 2018[^sc18]. The detailed set-up of our
experiments is available [^rate-experiments].

Our experimental procedure is as follows:

-   We randomly selected combinations of unsatisfiable instances and
    solvers from the main track. Running all possible combinations would take
    several CPU years in the worst case. Taking a sample of reasonable size
    seems to give good results already. [Table 1](#summary_table) shows a
    summary of how much of the available data we have analyzed.


-   If a solver had timed out for a particular instance during the
    competition, we skip that combination of solver + instance because we
    expect a timeout.

-   Firstly, the solver is run to create a proof, then all checkers are
    run. For `rate` and `DRAT-trim`, we verify the produced LRAT proof with
    the verified checker [^acl2].

-   We used the same limits as in the SAT competition - 5000 seconds CPU
    time and 24 GB memory using runlim [^runlim]. For checking the timeout
    is 20000 seconds, which is also consistent with the competition.

-   Since the machine we used for benchmarking has 32 cores, we used GNU
    parallel [@Tange2018] to run that many jobs simultaneously. Note that
    this parallelization slows down the solvers and checkers, most likely due
    to increased memory pressure. However, we believe that it is still a just
    comparison as the checkers seem to be affected equally. Some solvers timed
    out (unlike during the competition), likely due to the high system load.

```{.table #summary_table file="t/summary.csv" caption="The extent of our analysis."}
```

Comparison of Checkers
----------------------

As discovered previously [@RebolaCruz2018], many current proofs are being
rejected under the semantics of specified DRAT. We believe that larger
proofs have a higher chance of being rejected (TODO back this up). In our
set of benchmarks only around one third of the proofs were accepted by
`rate` in the default configuration, while all of them are accepted by
`rate --skip-unit-deletions`.

As in [@RebolaCruz2018] we only compare the performance on proofs that
were accepted by all checkers, because a rejection makes the checker exit early.

- Please note that `rate -d` is equivalent to `rate --skip-unit-deletions`,
standing for the executions of `rate` checking operational DRAT.

- We present performance data as reported by `runlim` --- time in seconds
and memory usage in megabytes (2^20^ bytes).


Overall, the performance of the four checkers we analyze is very similar,
as can be seen by the boxplots for runtime (figure @fig:box-time) and memory
usage (figure @fig:box-space).

![Boxplot of checker runtimes across all proofs](p/box-time.svg){#fig:box-time}

![Boxplot of the checkers' memory usage across all proofs](p/box-space.svg){#fig:box-space}


In figure @fig:cactus-time and @fig:cactus-space we show the distribution of
performances across the most difficult proof instances.  Those plot suggest
that `gratgen` is slightly faster, and `DRAT-trim` is slightly slower than
`rate`. Moreover `rate`, and `rate --skip-unit-deletions` show roughly the
same distribution of performance.

![Cactus plot showing the distribution of checker runtimes](p/cactus-time.svg){#fig:cactus-time}

![Cactus plot showing the distribution of the checkers' memory usage](p/cactus-space.svg){#fig:cactus-space}

We take a closer look, comparing the performance of two checkers on each
instance, see figures @fig:cross-rate-d-rate, @fig:cross-rate-d-gratgen and
@fig:cross-rate-d-drat-trim.

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `rate`.
Each marker represents a proof instance.](p/cross-rate-d-rate.svg){#fig:cross-rate-d-rate}

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `gratgen`.
Each marker represents a proof instance.](p/cross-rate-d-gratgen.svg){#fig:cross-rate-d-gratgen}

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `DRAT-trim`.
Each marker represents a proof instance.](p/cross-rate-d-drat-trim.svg){#fig:cross-rate-d-drat-trim}

In figure @fig:cross-rate-d-rate we see that `rate` exhibits small differences
in specified and operational model.  Figure @fig:cross-rate-d-gratgen shows
that `gratgen` is faster than `rate` on almost all instances.  Similarly,
figure @fig:cross-rate-d-drat-trim shows that `rate` is faster than `DRAT-trim`
on most instances.

![Correlation of the number of reason deletions and
the absolute runtime overhead of checking specified
DRAT.](p/correlation-reason-deletions-time-delta.svg){#fig:correlation-reason-deletions-time-delta}

![Correlation of the number of reason deletions and the
absolute overhead in terms of memory usage of checking specified
DRAT.](p/correlation-reason-deletions-space-delta.svg){#fig:correlation-reason-deletions-space-delta}

Overhead of Reason Deletions
----------------------------

Figure @fig:correlation-reason-deletions-time-delta suggests that a
large number of reason deletions brings about some runtime overhead in
`rate` when checking specified DRAT as opposed to operational DRAT.
Curiously, a significant overhead in memory usage seems to occur only
on proofs with comparably few reason deletions, as illustrated by figure
@fig:correlation-reason-deletions-space-delta.

Note that this overhead also occurs for proofs that only contain redundant
reason deletions. For this class of proofs, the overhead could be easily
remedied with a small change to the algorithm.  However, it is not yet
clear to us how this should be done ideally.  If solvers produced proofs
with (redundant) reason deletions only after addition of the unit clause
replacing other reason clauses, this would be trivial to optimize for.
This class of proofs is the one implemented by the second patch variant from
[section 4][4. Solvers].

8. Conclusion
=============

We have provided some evidence to our hypothesis that checking specified DRAT is
as expensive as checking operational DRAT.

We encourage SAT solver developers to to apply our patch to their `MiniSat`-based
solvers in order to create proofs that are correct under either flavor and
do not need the workaround of skipping unit deletions.

9. Future Work
==============

While our checker for specified DRAT is not really any more useful than
one for operational DRAT in terms of checking SAT solvers' unsatisfiability
results, it might be useful for checking inprocessing steps with unit deletions
[@rebola2018two]. Additionally it can be extended to support new proof formats.

Current DRAT checkers keep the entire input proof and the resulting LRAT
certificate in memory. If the available memory is at premium, some changes
could be made to do backwards checking in a streaming fashion. Additionally,
the LRAT output could be streamed with some postprocessing to fix the
clause IDs.

It might be possible to forego DRAT completely and directly generate LRAT
in a solver which is done by the solver `varisat`[^varisat]. This removes
the need for a complex checker at the cost of a larger proof artifact.


[^acl2]: <https://github.com/acl2/acl2/>
[^rupee]: <https://github.com/arpj-rebola/rupee>
[^rate]: <https://github.com/krobelus/rate>
[^sc18]: <http://sat2018.forsyte.tuwien.ac.at/>
[^rate-experiments]: <https://github.com/krobelus/rate-experiments>
[^runlim]: <http://fmv.jku.at/runlim/>
[^fix-revise-watches]: <https://github.com/arpj-rebola/rupee/compare/b00351cbd3173d329ea183e08c3283c6d86d18a1..b00351cbd3173d329ea183e08c3283c6d86d18a1~~~>
[^toml]: <https://github.com/toml-lang/toml>
[^patch-MapleLCMDistChronoBT]: <https://github.com/krobelus/MapleLCMDistChronoBT/commit/add-unit-before-deleting-locked-clause/>
[^patch-MapleLCMDistChronoBT-keep-locked-clauses]: <https://github.com/krobelus/MapleLCMDistChronoBT/commit/keep-locked-clauses/>
[^patch-MiniSat]: <https://github.com/krobelus/minisat/commit/add-unit-before-deleting-locked-clause/>
[^patch-MiniSat-keep-locked-clauses]: <https://github.com/krobelus/minisat/commit/keep-locked-clauses/>
[^suggestion-add-units]: <https://github.com/msoos/cryptominisat/issues/554#issuecomment-496292652>
[^mergesat-pr]: <https://github.com/conp-solutions/mergesat/pull/22/>
[^cadical]: <http://fmv.jku.at/cadical/>
[^varisat]: <https://github.com/jix/varisat/>
[^varisat-pr]: <https://github.com/jix/varisat/pull/66/>

References
==========
