---
title: Implementation of Complete and Efficient DRAT Proof Checking
author: Johannes Altmanninger
bibliography: references.bib
csl: ieee.csl
---

# View As

  ------------------- ---------------------------- -----------------
  [Source](README.md) [Markdown](README.markdown)  [PDF](README.pdf)
  ------------------- ---------------------------- -----------------

::: {.abstract}
**Abstract:**
Clausal proof format DRAT is the de facto standard way to certify SAT
solvers' unsatisfiability results.  State-of-the-art DRAT checkers ignore
deletions of unit clauses, which means that they are checking against a
proof system that differs from the specification of DRAT.  We demonstrate
that it is possible to implement a competitive checker that honors unit
deletions at small runtime overhead compared to the total checking time.
Many current proofs are incorrect under the DRAT specification, because
they contain spurious unit deletions. We present patches for competitive SAT
solvers to produce correct proofs with respect to the specification and make
checking thereof much simpler.
:::

1. Introduction
===============

The problem of Boolean satisfiability (SAT) is an archetypical problem in
computer science. In past decades, there has been significant progress in
the are of SAT solver technology. As a result of the high complexity of SAT
solvers, they have had bugs leading to incorrect results. To protect against
these, there are checkers that validate a solver's output. Satisfiable answers,
i. e. models, are trivial to validate in linear time. However, if there
is no model, the solver needs to give a proof of unsatisfiability. A proof
checker is a comparably simple program that verifies the latter. The proof
format that is widely used today is called DRAT (delete resolution asymmetric
tautologies). A DRAT proof is a sequence of lemmas (clause introductions)
and clause deletions where the lemmas need to satisfy redundancy property RAT.

It has been discovered [@rebola2018two] that state-of-the-art proof checkers
are not faithful to the specification of DRAT proofs [@Wetzler_2014]. They
ignore deletions of unit clauses in proofs because these would break invariants
in their data structures that are non-trivial to restore in an efficient
way. We refer to the original definition as *specified* DRAT and to the one
that is actually implemented by state-of-the-art checkers as *operational*
DRAT [@rebola2018two].

There are three distinct contributions in this work:

1. An implementation of a checker for *specified* DRAT that includes the
most important optimizations present in other checkers.  This allows us
to provide limited empirical evidence that checking *specified* DRAT is,
on average, not more expensive than *operational* DRAT although
it brings about a great increase complexity which would be unmotivated
if proofs did not contain reason deletions.

2. An extension of the SICK format that justifies the incorrectness of a proof.

3. Patches for MiniSat-based solvers to make them generate proofs that are
correct under either flavor of DRAT by not deleting reason clauses.

The rest of this paper is organized as follows: In [the following
section][2. Preliminaries] we will introduce preliminary knowledge about
logic, SAT solving and proofs of unsatisfiability.  After taking a look at
existing checkers throughout [Section 3][3. Existing Checkers], in [Section
4][4. Implementation] we will discuss the implementation of our checker,
which is our first contribution. The SICK format along our extension will be
described in [Section 5][5. SICK Format].  Experimental results are presented
in [Section 6][6. Experimental Evaluation].  Our third contribution is a
proposal on how to change solvers to produce correct proofs and can be found
in [Section 7][7. Solvers].  Finally, we draw a [conclusion][8. Conclusion]
a conclusion and give outlook on [future work][9. Future Work] on the area
of proof checking.


2. Preliminaries
================

Propositional Logic
-------------------

Boolean satisfiability operates on the domain of propositional logic.
A formula in propositional logic is either an atomic variable or a function
symbol applied to other (sub-)formulas.  An interpretation maps variables
to the Boolean domain and function symbols to Boolean functions of their
respective arity. A formula under an interpretation has a Boolean value.
If this value is true, that interpretation is called a model.

We only consider three different function symbols: the unary negation
($\neg$), binary conjunction ($\land$) and disjunction ($\lor$).
The negation of atomic variable $x$ is denoted by $\overline{x}$.
All interpretations that follow give the obvious semantics to these functions,
we usually call them assignments.

Negation-normal form (NNF) is a class of propositional formulas where
negation may only be applied to variables and not to any other subformula.
A formula in conjunctive normal form (CNF) is a conjunction of clauses,
where a clause is a disjunction of literals. A model for a formula in CNF
necessarily satisfies each clause in the formula.  A literal is a variable
or a negation of a variable.  Every propositional formula can be converted
to an equivalent formula in CNF.  Two formulas are equivalent if they have
the same set of models.

We treat a (partial) interpretation as set of literals, with a variables
and negated variables in the set being mapped to true and false respectively.
Literals that are not in the set are not assigned any value.


SAT solving
-----------

A formula is satisfiable if there exists a model for it.  A sound and complete
SAT solver takes as input a formula in CNF and finds a single model if it
exists, or gives a unsatisfiability result. Due to the complexity of SAT
solvers and ensuing bugs, it might be dangerous to trust their answers.
Therefore an unsatisfiability result is accompanied by a proof.

While searching for a model, a solver builds up a partial interpretation
which we usually call trail or assignment. Note that it includes the order
in which the literals where added.

Unit Propagation
----------------

If a formula contains a unit clause, any model must contain the unit literal.
Then a solver can perform unit propagation add the unit to the trail, discard
any clause containing it (because they will be satisfied by the unit),
and remove any of its negations from the remaining clauses.  The last step
may spawn new units and triggers further propagation. A conflict arises as
soon as two literals of opposing polarity are assigned which shows that the
formula is unsatisfiable.

The majority of solving time in state-of-the-art SAT solvers is spent
in unit propagation. The data structure to keep track of which clauses
can trigger propagations is called the two-watched-literal scheme
[@Moskewicz:2001:CEE:378239.379017]. It consists of a watchlist for each
literal, which is an array of clause references. All the clauses in the
watchlist of some literal said to be *watched by* that literal.
The essential invariant is that each clause is watched on two literals -
the "watches".  To check if a clause is unit, it suffices to look
at the watches. This property is maintained by Invariant 1 from [@RebolaCruz2018].

**Invariant 1.** If a clause is watched on literals l and k, and the current
trail I falsifies l, then I satisfies k.


Clausal Proofs
--------------

A formula in CNF is modeled as a multiset of clauses.  Each step in a
clausal proof adds a clause to the current formula, or deletes one from it.
A solver or checker maintains a partial model or trail of forced literals.
After adding a clause that is unit (all literals falsified except for a
single unassigned *unit literal*) w.r.t. the current partial model, it is
propagated. Every unit literal that is added to the trail is associated with
the clause which we call the *reason*.

Transformations on formulas can be equivalence-preserving, or
satisfiability-preserving.  Obviously, deleting a clause is neither, but
if some formula is unsatisfiable after deleting a clause, it also is before
doing so.

Redundancy Properties
---------------------

A clause $C$ is a *asymmetric tautology* (AT) with respect to formula $F$
if and only if $F \vdash_1 C$ which means that unit propagation in $F \cup \{
\{\overline{l}\} \,|\, l \in C \}$ leads to a conflict.  ATs are implied by
the formula and therefore redundant, while being fast to compute compared
to all logical consequences ($\vdash$). We will usually call an AT "RUP" -
as they are computed by reverse unit propagation.

A clause $C$ is a *resolution asymmetric tautologies* (RAT)
[@inprocessingrules] on some literal $l \in C$ with respect to formula $F$
whenever for all clauses $D \in F$ where $\overline{l} \in D$, the resolvent
$C \cup (D \setminus \{\overline{l}\})$ is RUP.

Addition of RUP or RAT clauses without new variables is equivalence-preserving.
Same holds for deletion of RUPs, while deletion of RATs is only
satisfiability-preserving.

Another property that generalizes RAT is called *propagation redundancy*
(PR) [@Heule_2017].

Deletions
---------

SAT solvers learn clauses based on conflicts (CDCL).  These clauses are
added to the proof until a top-level conflict is derived eventually.

Resolution refutations are exponential in the size of the formula, as are DRAT
proofs. To substantially reduce checking efforts, clause deletion information
has been added to proof formats [@Heule_2014].  Clauses that are subsumed
by some other clause can be safely deleted without losing information.

Deleting a reason clause generally changes the set of implied literals, i.e.
the cone of influence (see [@RebolaCruz2018]) of the associated unit literal
is removed from the trail.  However, if every literal in the cone is still
implied after deleting a reason clause, then the deletion can be performed
without loss of information.  We call this special case a *redundant reason
deletion*, distinguishing it from a *reason deletion* where information is
necessarily lost.  A more general term than both would *unit deletion*,
comprising deletions of clauses where exactly one literal is satisfied
and all other literals are falsified.

DRAT Proofs
-----------

Proof based on RUP are not expressive enough to cover all inprocessing
techniques in modern SAT solvers. For this reason, more powerful
property RAT is used today[@rat]. Clause deletion was introduced to make
checking more efficient[@Wetzler_2014].

A DRAT proof is a clausal proof with deletions where every lemma is RAT.

LRAT Proofs
-----------

The runtime and memory usage of DRAT checkers can exceed the ones of the
solver that produced the proof. The resulting need to have a DRAT checker be as
efficient as possible makes it difficult to implement a mechanically verified
checker. This is remedied by making the DRAT checker output an optimized (=
small) and annotated proof in LRAT format [@cruz2017efficient]. Checking this
proof does not require blind propagation and there are verified implementations
available[^acl2].

Backwards Checking
------------------

While searching, SAT solvers can not know, which learned clauses are useful
in a proof, so they simply add all learned clauses. This means that many
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

As explained in [@RebolaCruz2018], formulas without reason deletions have
a stack that is growing monotonically. When doing backwards checking,
it is trivial to undo the propagations done after a lemma introduction
by merely truncating the stack.

However, when there are reason deletions it is not as simple.  During the
forward pass, when a reason clause is deleted its associated unit is
unassigned.  If this unit was necessary to propagate some other unit, this
may be unassigned as well, and so on. All these literals form the cone of
influence of the first unit and are record in the checker, alongside their
positions in the trail, and their reasons.

The recorded information can then be used in the backward pass to patch
the trail at any step that is a reason deletion, in order for the trail to
be exactly as it was during the forward phase. The tricky part here is to
correctly restore the watch invariant in all affected clauses. TODO

3. Existing Checkers
====================

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

GRAT toolchain
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
DRAT proofs tend to contain sequences of RAT lemmas with the same pivot, in
which case they only compute the list of RAT candidates once per sequence and
reuse. We did not implement that because the number of RAT introductions in
our benchmarks is negligible when compared to the number of RUP introductions.

We also implement GRAT generation in our tool which. However, it seems that
the `gratchk` tool is not designed to handle unit deletions (apparently they
are ignored) so proofs with unit deletions will fail.

`rupee` [^rupee]
----------------

This is the original implementation of the algorithm to handle
reason deletions. We use exactly the same algorithm.  During our research we
found an issue in the implementation which was fixed [^fix-revise-watches].
We also use their representation of size-one clauses: they are padded
by a special literal $\bot$ in order to keep the two-watched-literal
[@Moskewicz:2001:CEE:378239.379017] data structure simple.

Based on a limited set of benchmarks, `rupee` appears to be an order of
magnitude slower than `DRAT-trim` [@RebolaCruz2018].

However, we believe that this overhead is primarily not a consequence of
the algorithmic differences but due to differences in the parsing stage
[^rupee-parsing] and other implementation details.

[^rupee-parsing]: Both `rupee` and `DRAT-trim` use a fixed-size hash table
to locate deleted clauses but `rupee`'s is smaller by one order of magnitude,
which may explain most of the difference in performance.

Additionally `rupee` does not use core-first unit propagation while the
other checkers do. This is important for fast checking on some instances.

4. Implementation
=================

The implementation (`rate`) is available [^rate].

Features
--------

- check DRAT (default) and PR (file extension `.pr` or `.dpr`) proofs
- output core lemmas as DIMACS or LRAT for accepted proofs
- output certificate of unsatisfiability for rejected proofs, see [SICK format]
- competitive performance due to double-sweep checking with
  core-first unit propagation
- option to ignore unit deletions (`--skip-unit-deletions`)
- decompress input files (Gzip, Zstandard, Bzip2, XZ, LZ4)

- The debug build comes with lots of assertions, including checks for
arithmetic overflows and lossy narrowing conversions.

We initially reserved 62 bits to identify clauses while `DRAT-trim` uses 30.
Unfortunately, this caused issues with memory consumption because we need to
encode clause hints in the LRAT proof which is larger than the input proof
and needs to be kept in memory until the proof checking is complete. Future
proof formats should allow checking without keeping the entire proof in
memory, although backwards checking might make this difficult.  In order
to make `rate` comparable to `DRAT-trim` in terms of memory consumption,
we also use 30 bits for clause hints in the LRAT output.

5. SICK Format
==============

When a proof is found to be incorrect, our tool outputs information
to show what exactly failed.
This helps us in making sure that a proof is actually refutable and it
can help developers to find bugs when they generate proofs.
The incorrectness certificate is of our variant of the SICK format which is
a subset of TOML[^toml] and can be verified by our tool `sick-check`.

Our contribution consists of extending the format to support PR and permit
multiple witnesses which is necessary for some DRAT proofs.

Example SICK certificate:
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

The format follows this grammar:

```
SICK := Intro Witness*
Intro := ProofFormat ProofStep NaturalModel
ProofFormat := 'proof_format' '='
		( "DRAT-arbitrary-pivot"
		| "DRAT-pivot-is-first-literal"
		| "DPR"
		)
ProofStep := 'proof_step' '=' Integer
NaturalModel := 'natural_model' '=' ListOfLiterals
Witness := FailingClause FailingModel [ Pivot ]
FailingClause := 'failing_clause' '=' ListOfLiterals
FailingModel := 'failing_model' '=' ListOfLiterals
Pivot := 'pivot' '=' Literal
```

Meaning:

- `proof_format` describes the proof format to use.
   - `DRAT-arbitrary-pivot`: Implies DRAT checking. This requires one witness
   (counter example) for each possible pivot in the failing lemma. The pivot
   has to be specified for each witness (unlike for any other format).
   - `DRAT-pivot-is-first-literal`: Similar but there is only one witness
   as the pivot is assumed to be the first literal in the lemma.
   - `DPR`: For DPR checking. Only one witness is necessary.
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
when performing the redundancy check. When checking for RAT this is the set of
literals that are propagated along the reverse resolvent.
- `pivot`: Only necessary for format `DRAT-arbitrary-pivot`, this specifies
  the pivot that was used for each witness.

Note that if the failed lemma is the empty clause, no witness is needed.

6. Experimental Evaluation
==========================

To evaluate our tool, we performed experiments on proofs produced by
solvers from the SAT competition 2018[^sc18]. The detailed set-up of our
experiments is available [^rate-experiments].

Our experimental procedure is as follows:

-   We randomly selected combinations of unsatisfiable instances and
    solvers from the main track. Running all possible combinations would
    take several CPU years in the worst case, but sampling seems to give
    good results still.

-   If a solver had timed out for a particular instance during the
    competition, we skip that combination because we will most likely not
    be able to produce a proof within the time limit.

-   Firstly, the solver is run to create a proof, then all checkers are
    run. For `rate` and `DRAT-trim`, we verify the produced LRAT proof with
    the verified checker [^acl2].

-   We used the same limits as in the SAT competition - 5000 seconds CPU
    time and 24 GB memory using runlim [^runlim]. For checking the timeout
    is 20000 seconds, which is also consistent with the competition.

-   Our benchmarking system has 32 cores, we used GNU parallel
    [@Tange2018] to run that many jobs simultaneously. Note that this
    parallelization slows down the solvers and checkers, most likely due to
    increased memory pressure. However, we believe that it is still a just
    comparison as the checkers seem to be affected equally. Some solvers
    timed out due to this, so we have less data for difficult instances.

[Table 2](#summary_table) shows a summary of how much of the available
data we have analyzed.

```{.table #summary_table file="t/summary.csv" caption="The extent of our analysis."}
```

Specified vs. Operational DRAT
------------------------------

As discovered previously [@RebolaCruz2018], many proofs are rejected under
the semantics of specified DRAT. We believe that larger proofs have a higher
chance of being rejected. In our set of benchmarks only around one third of
the proofs were accepted by `rate` in the default configuration while
all of them are accepted by `rate --skip-unit-deletions`.

For the proofs that are accepted by both, we compare their performance. A
large number of reason deletions seems cause some overhead as
observed in figure @fig:correlation-0. Looking at the [corresponding
table](t/difference-accepted.csv), there are only a few instances with an
excessive number of reason deletions. Some of those are being checked slower
when performing reason deletions, however there are also instances where
the opposite is true.

![Overhead of `rate` versus `rate
--skip-unit-deletions`](p/correlation-0.png){#fig:correlation-0}

Comparison to other checkers
----------------------------

Compared to other checkers, `rate` seems have a similar performance.

We present performance data as reported by `runlim` --- time in seconds
and memory usage in megabytes (2^20^ bytes).

Based on our data, there seems to be no significant difference in the
distribution of runtime and memory usage between other state-of-the-art
checkers and ours (with or without unit deletions).

![runtime](p/performance-6.png)
![memory usage](p/performance-7.png)

7. Solvers
==========

As stated already in [@RebolaCruz2018], most solvers at competitions
emit proofs with reason deletions.  The overwhelming majority of
solvers submitted to the main track of the 2018 SAT competition is
based on `MiniSat` or `CryptoMiniSat`.  Only their proofs contain reason
deletions.  We provide patches to prevent that for `MiniSat` version 2.2
[^patch-MiniSat] and the winner of the main track of the 2018 SAT competition
[^patch-MapleLCMDistChronoBT].  They same method can be applied to other
`MiniSat`-based solvers.

The patch for MiniSat is displayed below. Let us explain how it works.

Used during the simplification phase, the method `Solver::removeSatisfied`
takes a collection of clause references and removes the ones that are
satisfied from the clause database while emitting a deletion in the DRAT
output for those clauses at the same time.  Note that it is only called
at decision level zero, which means that those clauses will be satisfied
indefinitely for the rest of the solving time.

In MiniSat, *locked* clauses are reasons for some literal in the trail.
Previously, `Solver::removeSatisfied` would also deleted locked clauses,
however, the corresponding assignment was not undone.  Remember that the trail
here is the set of literals implied by unit propagation on the formula.  If the
reason for some literal is gone, then it might not be implied any longer.
This suggests that a locked clause is implicitly kept in the formula, even
though it is deleted.  To match this solver's behavior, current DRAT checkers
do not undo any assignments when deleting clauses.

There are two obvious solutions to this problem.

1. Do not remove locked clauses during simplification[^patch-MiniSat-keep-locked-clauses].

2. Before to removing locked clauses, emit the corresponding
propagated literal as addition in the DRAT proof.  Suggested by Mate
Soos[^suggestion-add-units], this option is also the preferred one to two
other solver authors[^mergesat-pr] [^varisat-pr] .

Here is the diff for our MiniSat patch of the latter variant:

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

8. Conclusion
=============

We have provided some evidence to our hypothesis that checking specified DRAT is
as expensive as checking operational DRAT.

We encourage SAT solver developers to to apply our patch to their MiniSat-based
solvers in order to create proofs that are correct under either flavor and
do not need the workaround of skipping unit deletions.

9. Future Work
==============

While our checker for specified DRAT is not really any more useful than one
for operational DRAT in terms of checking SAT solvers' unsatisfiability
results, it might be useful for checking inprocessing steps with unit
deletions. Additionally it can be extended to support new proof formats.

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
[^patch-MiniSat]: <https://github.com/krobelus/minisat/commit/add-unit-before-deleting-locked-clause/>
[^patch-MiniSat-keep-locked-clauses]: <https://github.com/krobelus/minisat/commit/keep-locked-clauses/>
[^suggestion-add-units]: <https://github.com/msoos/cryptominisat/issues/554#issuecomment-496292652>
[^mergesat-pr]: <https://github.com/conp-solutions/mergesat/pull/22/>
[^varisat]: <https://github.com/jix/varisat/>
[^varisat-pr]: <https://github.com/jix/varisat/pull/66/>


References
==========
