---
title: Complete and Competitive DRAT Proof Checking
author: Johannes Altmanninger
bibliography: references.bib
date: \today
csl: ieee.csl
header-includes: |
        \usepackage{todonotes}
---

::: {.abstract}
**Abstract:** Clausal proof format DRAT is the de facto standard way to certify
SAT solvers' unsatisfiability results.  State-of-the-art DRAT checkers ignore
deletions of reason clauses, which means that they are checking against a proof
system that differs from the specification of DRAT.  We demonstrate that it
is possible to implement a competitive checker that honors reason deletions.
Many reputable SAT solvers produce proofs that are incorrect under the DRAT
specification, because they contain spurious reason deletions. We present
patches for competitive SAT solvers to produce correct proofs with respect
to the specification.
:::

1. Introduction
===============

In past decades, there has been significant progress in SAT solver
technology. As a result of the high complexity of SAT solvers they have
had documented bugs [@BrummayerBiere-SMT09] [@BrummayerLonsingBiere-SAT10].
To protect against these, there are checker programs that verifiy a solver's
result. The result *"satisfiable"* is given with a model which is trivial
to validate in linear time.  The converse result, *"unsatisfiable"*, can be
certified with a proof of unsatisfiability given by the solver. An independent
proof checker can verify such proofs.

In SAT competitions, solvers are required to give a proof in the DRAT format
alongside an unsatisfiability result.  This proof can be thought of as a
trace of the solver's execution, containing information on which clauses
(i.e., constraints) are added to and deleted from the solver's formula which
acts as knowledge base. While deletions are not strictly necessary to produce
the unsatisfiability result in either solver or checker, they are essential
for doing that efficiently.

A family of solvers produce proofs containing certain reason clause deletions,
yet these solvers operate as if those clauses were not deleted.  To accomodate
for this, state-of-the-art proof checkers ignore instructions of all reason
clauses, which includes those spurious deletions. Consequently, the checkers
are not faithful to the specification of DRAT proofs [@rebola2018two].

We refer to the original definition of the proof format as *specified* DRAT
and to the one that is actually implemented by state-of-the-art checkers as
*operational* DRAT [@rebola2018two]. The classes of proofs accepted by these
two flavors of DRAT are incomparable.  Merely checking operational DRAT is
sufficient for current proofs of unsatisfiability, however, specified DRAT
can be a requirement for verifying solvers' inprocessing steps which are
employing reason deletions [@rebola2018two].

As proof checking time is comparable to solving time [@Heule_2014] it is
desirable to reduce the former as much as possible --- consider the problem
of the Schur Number Five, where solving took just over 14 CPU years whereas
running the DRAT checker on the resulting proof took 20.5 CPU years [@schur-5].
There exists an efficient algorithm for specified DRAT [@RebolaCruz2018],
adding quite some complexity on top of state-of-the art checking algorithms
for operational DRAT.  Previous empirical results for that algorithm suggest
that the class of proofs that today's solvers produce can be verified with
a checker of either flavor with roughly the same runtime and memory usage.
Those results, however, were based on a checker that could not compete with
other state-of-art checkers in terms of performance.

We have re-implemented the algorithm in combination with other necessary
optimizations to roughly match the performance of the fastest checkers.
Based on this implementation, we are able to provide more extensive results,
supporting the hypothesis that specified and operational DRAT are equally
expensive to check on an average real-world instance.  We also observe that
a high number of reason deletions tends to have a significant impact on
checking performance, making specified DRAT more expensive, and sometimes
less expensive too.

To show the incorrectness of a proof, it suffices show that a single clause
introduction, or lemma in the proof is incorrect.  We use a modified version
of the previously unpublished SICK incorrectness certificate format to give
information on why a lemma cannot be derived.  This certificate can be used
to verify the incorrectness of the proof efficiently and help developers
find bugs in proof generation procedures.

To sum up, there are three distinct contributions in this work:

1. We indicate why solvers generate those spurious deletions and provide
patches for top solvers to make them generate proofs without them, which
are therefore correct under either flavor of DRAT.

2. Our extension to the SICK certificate format is introduced.

3. We present the implementation of our checker for specified DRAT
that includes the most important optimizations present in other checkers.
This allows us to provide empirical evidence that checking specified DRAT
is, on average, as expensive as operational DRAT, albeit more complicated.

The rest of this paper is organized as follows: In [the following
section][2. Preliminaries] we will introduce preliminary knowledge about
SAT solving, proofs of unsatisfiability, checking algorithms, the problem
with reason deletions and existing checkers.  After establishing novel
terminology in [the following section][3. Two Kinds of Reason Deletions],
our first contribution, a proposal on how to change solvers to produce
unambiguously correct proofs, can be found in [Section 4][4. Solvers].
The SICK format along our extension will be described in [Section
5][5. SICK Format].  The third contribution will be discussed in [Section
6][6. Checker Implementation] with experimental results being presented in
[the following section][7. Experimental Evaluation].  Finally, we draw a
[conclusion][8. Conclusion] and give outlook on [future work][9. Future Work]
in the area of proof checking.

2. Preliminaries
================

Notation
--------

A literal is a propositional variable, like $x$, or a negation of a variable,
denoted by $\overline{x}$. A clause is a disjunction of literals, usually
denoted by juxtaposition of the disjuncts, e.g. we write $xy\overline{z}$
for $x \lor y \lor \overline{z}$.

An assignment is a set of literals. All literals in an assignment are
considered to be satisified by that assignment.  Conversely, the negations
of those literals are falsified by that assignment.  Other literals are
unassigned.  If there are some unassigned literals, then the assignment
is partial.  We assume that an assignment never contains a literal in both
polarities.

SAT Solving
-----------

SAT solvers work on formulas in conjunctive normal form (CNF), conjunctions
of clauses.  A clause is satisfied by an assignment $I$ if any one literal in
the clause is satisfied by $I$.  A CNF formula is satisified by $I$ if each
of its clauses is satisfied by $I$.  An assignment that satisfies a formula is
called a model for that formula.  Two formulas $F$ and $G$ are *satisfiability
equivalent* if $F$ is satisfiable if and only $G$ is satisfiable.

A formula is satisfiable if there exists a model for it.  A SAT solver
takes as input a formula and finds a model if the formula is satisfiable.
Otherwise, the solver can provide a proof that the formula is unsatisfiable.
This proof needs to derive the unsatisfiable empty clause.

While searching for a model, a solver builds up a (partial) assignment.
Additionally it records the order in which the literals where assigned.
We call this data structure the *trail*.

SAT solvers search through the space all possible assignments.  They make
assumptions, adding literals to the trail that might be part of a satisfying
assignment.  The search space is greatly reduced by formula simplification,
such as unit propagation which will be introduced in the next subsection.
Simplification during search (interleaved with assumptions) is called
inprocessing, as opposed to preprocessing which precedes the first assumption.
Such simplifications can prune assignments that are definitely unsatisfiable,
by adding literals to the trail. These literals are said to be forced,
because they, unlike assumptions, are necessarily satisfied in any model that
extends the current trail.  If simplifications are done on a trail without
any assumptions, the trail is the set of top-level forced literals, the set
of literals that are part of any model.  These are essential for a checker
as we will see later.  Once the set of top-level forced literals falsifies a
clause, then the solver has derived the empty clause and therefore established
unsatisfiability of the current formula and also the input formula.

CDCL
----

Most modern SAT solvers implement Conflict Driven Clause Learning (CDCL).
Whenever a clause clause in the formula is falsified, this means that the
current set of assumptions can not be part of any model. Therefore a subset
of the assumptions is reverted and a *conflict clause* is learned, and added
to the formula to prevent the solver from revisiting those ill-advised
assumptions, effectively pruning the search space.  As the number of
clauses increases, so does memory usage and the time spent on formula
simplification. Because of this, learned clauses that are not considered
useful enough, are regularly deleted from the formula.

Unit Propagation
----------------

Given an assignment, a *unit clause* contains only falsified literals except
for a single non-falsified *unit literal*.

At any point during a solver's search, if the formula contains a unit clause,
any model extending the current trail must contain the unit literal, therefore
it is added as a forced literal. The unit clause is recorded as the *reason
clause* for this literal.  Everytime a literal $l$ is added to the trail, the
formula will be simplified by *propagating* $l$: any clause containing $l$ is
discarded because it will be satisfied $l$, and occurrences of $\overline{l}$
are removed from the remaining clauses. The latter step may spawn new unit
clauses and thus trigger further propagation.

As assumptions need to be undone many times during search, the implementation
of unit propagation does not actually delete clauses and literals, but
merely scans the formula for new units.  In order to efficiently keep track
of which clauses can become unit, competitve solvers and checkers use the
two-watched-literal scheme [@Moskewicz:2001:CEE:378239.379017]. It consists of
a watchlist for each literal, which is a sequence of clause references. All
the clauses in the watchlist of some literal are said to be *watched by*
that literal.  Each clause is watched by two literals, these are also called
the *watches*.  To check if a clause is unit, it suffices to look at the
watches given Invariant 1 from [@RebolaCruz2018] is maintained:

**Invariant 1.** If a clause is watched on literals $l$ and $k$, and the
current trail $I$ falsifies $l$, then $I$ satisfies $k$.

In particular, when literal $l$ is assigned, it is propagated by scanning
the watchlist of $\overline{l}$, thus visiting only clauses that are watched
on $\overline{l}$. Since their watch $\overline{l}$ is falsified, Invariant 1 might need to be restored.

Note that, as in [@RebolaCruz2018], clauses of size one are extended by a
single literal $\overline{\top}$ to make the manipulations of watches work
the same way for all clauses.

Clausal Proofs
--------------

A formula in CNF is a multiset of clauses.  Each step in a clausal proof
adds a clause to the current formula, or deletes one from it.  These steps
should be exactly the clause introductions and clause deletions that a
solver performs.  As a result, a checker can reproduce the formula as well
as the set of top-level forced literals at each step, and finally derive
the empty clause just like the solver did.

Redundancy Properties
---------------------

A clause $C$ is redundant in $F$ if $F$ and $F \cup \{C\}$ are satisfiability
equivalent [@Heule_2017].  Note that $C$ is not necessarily a
 logical consequence of the formula [@philipp_rebola_unsatproofs].

There are various criteria of redundancy, with different levels of expressivity
and computational costs.  Each lemma in a clausal proof must be redundant
according to the proof's redundancy criteria.

**Redundancy Criteria RUP:** a clause $C$ is RUP (reverse unit propagation)
in formula $F$ if unit propagation in $F \cup \{ \{\overline{l}\} \,|\,
l \in C \}$ can derive the empty clause.

The *resolution rule* states that for literal $l$ and clauses $C$ and $D$
where $l \in C$ and $\overline{l} \in D$, the conjunct of $C$ and $D$ implies
$(C \setminus \{l\}) \cup (D \setminus \{\overline{l}\})$. The derived clause
is called the *resolvent on $l$ of $C$ and $D$*. $D$ is called a *resolution
candidate* for $C$.

**Redundancy Criteria RAT:** a clause $C$ is a *resolution asymmetric
tautology* (RAT) [@inprocessingrules] on some literal $l \in C$ with respect
to formula $F$ whenever for all clauses $D \in F$ where $\overline{l} \in D$,
the resolvent on $l$ of $C$ and $D$ is RUP in $F$.

Deletions
---------

Proofs based on the resolution rule are exponential in the size of the
formula, as are ones based on RUP or RAT.  A proof solely consisting of
clause introductions will result in the checker suffer from the huge number
of clauses as described in [CDCL].  To counteract this, clause deletion
information has been added to proof formats, making the proof checking time
comparable to solving time [@Heule_2014].

DRAT Proofs
-----------

Proof based on RUP alone are not expressive enough to cover all inprocessing
techniques in modern SAT solvers. For this reason, more powerful criteria
RAT is used today [@rat]. Clause deletion was introduced to make checking
more efficient [@Wetzler_2014].

A DRAT (*delete resolution asymmetric tautology*) proof is a clausal proof
with deletions where every lemma is RAT.  Given that a solver emits all
learned clauses and clause deletions in the DRAT proof, the checker can
reproduce the exact same formula that the solver was working on.

In practice, most lemmas in proofs are RUP, so a checker first computes for
RUP and only if that fails, falls back to RAT.

While deletions were added to proofs to optimize checking runtime, they
can also be enable additional inferences due to RAT being non-monotonic
[@philipp_rebola_unsatproofs].

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
for each resolution candidates and all unit clauses that are necessary to
derive a the empty clause to show that the resolvent is a RUP.

Forward Checking
----------------

The obvious way to verify that a proof is correct consists of performing each
instruction in the from the first to one last one, while checking each lemma.

Backwards Checking
------------------

While searching, SAT solvers can not know, which learned clauses are useful
in a proof, so they simply add all of them as lemmas. This means that many
lemmas might not be necessary in a proof of unsatisfiability.

To avoid checking superfluous lemmas, the proof is checked backwards ---
only lemmas that are transitively necessary to derive the empty clause are
checked [@Heule_2013].

This requires two passes: a forward pass performing unit propagation
[@RebolaCruz2018] until the empty clause is derived, and a backward pass
that actually checks each required clause introduction.

An *unsatisfiable core*, for short *core* is an unsatisfiable subset of
an unsatisfiable formula. With backwards checking, a core is eventually
computed and only core lemmas are checked.  At the end of the forward pass,
conflict analysis adds to the core all clauses that were required to derive
the empty clause.  This is done by a depth-first search in the graph induced
by the reason clauses: starting from the clause that was falsified, the
clause is added to the core and, for each of its literals $l$, the same is
done recursively for the reason for $\overline{l}$.

Subsequently during the backward pass, only core lemmas are checked. During
those RUP and RAT checks, after each derivation of an empty clause the same
conflict analysis as described above takes place, which can add more clauses
to the core.

A side product of this core computation is a *trimmed proof*, consisting
of all core lemmas. The LRAT output is based on the trimmed proof.

Core-first Unit Propagation
---------------------------

In order to keep the core small and reduce checking costs, core-first unit
propagation was introduced [@Heule_2013].  It works by doing unit propagation
in two phases:

1. Propagate exhaustively using all clauses that are already known to be in
the core.
2. Consider non-core clauses: propagate only the first unit found and go
to 1.  If there is no unit found, the propagation has reached its fixed-point
without deriving the empty clause.

Which results in a local minimum of clauses being added to the core.

Reason Deletions
----------------

As explained in [@RebolaCruz2018] when checking a proof without deletions
of reason clauses, the trail grows monotonically, that is, it never shrinks
at any proof step during the forward phase. Therefore, during the backwards
phase, it is trivial to undo the propagations done after a lemma introduction
by merely truncating the stack. This also maintains Invariant 1, making sure
the watchlists will always find all unit clauses.

When a proof with reason deletions is checked under specified DRAT, the
algorithm from [@RebolaCruz2018] is required to restore Invariant 1 in the
backward pass. The rest of this subsection tries to explain this algorithm.
An understanding of the latter is not required to understand the contributions
in this paper but it is included for completeness.

Let us now consider a proof with reason deletions.  A reason deletion
means that a clause will be deleted from the formula in the forward pass
and re-introduced in the backward pass.  This requires adding it to the
watchlists and removing it respectively.

During the forward pass, whenever a reason clause is deleted its associated
unit literal is unassigned.  If this literal was necessary to propagate
some other unit, that one may be unassigned as well, and so on. All these
literals form the *cone of influence* (see [@RebolaCruz2018]) of the first
unit literal and are recorded in the checker, alongside their positions in
the trail, and reasons clauses.

The recorded information can then be used in the backward pass to patch the
trail at the reason deletions in order for the trail to be exactly as it
was during the forward phase. The tricky part here is to correctly restore
the Invariant 1 in all affected clauses.

When a reason deletion is processed during the backwards phase, each
literal in the cone will be reintroduced into the trail at the recorded
position.  Consider literal $l$ in the cone. Before applying the backwards
deletion it could have been satisfied or unassigned (but not falsified).
After reintroducing it, it is assigned. Therefore, a clause containing
$\overline{l}$ might become unit without the checker noticing.  Because of
this, the watchlists of all reverse cone literals $\overline{l}$ have to be
traversed to restore the watch invariant.  Each of those clause is watched
on falsified literal $\overline{l}$. This watch and possibly the other watch,
too, need to be swapped with other literals to restore Invariant 1.

In case the clause has at least two non-falsified literals, the watches can 
be set to any two out of those.

However, if the clause has only one non-falsified literal (it is necessarily
satisifed because of Invariant 1), then the other watch must be the most
recently falsified literal [@RebolaCruz2018; Example 5]. Let us illustrate
the reason for this by means of an example. Imagine clause $xyz$ with $I =
\{x, \overline{y}, \overline{z}\}$.  It is watched on the first two literals,
$x$ and $y$.  A clause introduction step is processed backwards which causes
$x$ and $\overline{z}$ to be unassigned, e.g. $I' = \{\overline{y}\}$ but the
watches are not touched, hence Invariant 1 is violated.  In particular, during
a RUP check, $\overline{z}$ could be assigned, making the clause unit which
would go unnoticed, because $z$ is not watched.  To avoid such a situation,
after performing a deletion instruction backwards, such a falsified watch must
be set to the most recently falsified literal.  This ensures that, during
any backwards introduction, if the satisfied watch $x$ is being unassigned,
the other watch will also be unassigned, thus restoring Invariant 1.

Existing Checkers
-----------------

Previous work has yielded checkers which we draw upon heavily. In fact,
our implementation contains no algorithmic novelties but merely combines
the ideas present in existing checkers.

`DRAT-trim`
-----------

The seminal reference implementation; Marijn Heule's `DRAT-trim` can produce an
optimized proof in LRAT format. We use their way of producing LRAT proofs and
make sure that all our proofs are accepted by the verified checker [^acl2].
This gives us confidence in the correctness of our implementation and allows
for a comparison of our checker with `DRAT-trim` since they do roughly the
same thing except for the reason deletions.

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

We also implement GRAT generation in our tool. However, it seems that the
`gratchk` tool is not designed to handle reason deletions (apparently they
are ignored) so it will fail to handle our GRAT certificates for proofs with
reason deletions.

Amongst state-of-the-art DRAT checkers, `gratgen` is arguably the easiest
to understand, so we advise interested readers to study that.

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

3. Two Kinds of Reason Deletions
=============================

Here we clarify which reason deletions are actually problematic.

Deleting a reason clause generally shrinks the trail.  However, if, and only
if there is another clause that can act as reason for the same literal at
any point during unit propagation after removing the reason clause, then
the set of literals in the trail does not change.  We call this special
case a *redundant reason deletion*, and the other case a *non-redundant
reason deletion*.  An simple example for a redundant reason deletion would
be the deletion of a size-one reason clause that occurs twice in the formula.

Note that the term *unit deletion* comprises deletions of any unit clause,
that is, reason deletions and other deleted units that were not propagating.

A proof of unsatisfiability generated by a SAT solver should not contain
any non-redundant reason deletions.  Other current checkers can report unit
deletions and reason deletions but they do not distinguish between redundant
and non-redundant reason deletions.  Our tool also outputs the number of
non-redundant reason deletions [^reason-deletions-shrinking-trail]. This
might be useful to sanity-check SAT solvers' proof generation procedures.

Given a proof without non-redundant reason deletions, checkers for
*operational* and *specified* DRAT behave exactly the same way.

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
of the search.

In `MiniSat`, *locked* clauses are reasons for some literal in the trail.
Currently, `Solver::removeSatisfied` also deletes locked clauses, however,
the induced assignments are not undone.  This suggests that a locked clause
is implicitly kept in the formula, even though it is deleted.  To match this
solver's behavior, current DRAT checkers ignore deletions of reason clauses,
which means they do not undo any assignments when deleting clauses.

There are two obvious possible changes to `MiniSat` to produce proofs that
do not require this workaround of ignoring reason deletions when checking.

1. Do not remove locked clauses during simplification.

2. Before to removing locked clauses, emit the corresponding
propagated literal as addition in the DRAT proof.  Suggested by Mate
Soos[^suggestion-add-units], this option is also the preferred one to the
authors of `mergesat`[^mergesat-pr] and `varisat`[^varisat-pr].  Additionally,
this is implemented in `CaDiCaL's`[^cadical] preprocessor.

We provide patches implementing these for `MiniSat` version 2.2
(1.  [^patch-MiniSat-keep-locked-clauses] and 2.[^patch-MiniSat]),
and the winner of the main track of the 2018 SAT competition
(1.[^patch-MapleLCMDistChronoBT-keep-locked-clauses] and
2.[^patch-MapleLCMDistChronoBT]).

The same methods can be applied easily to other `MiniSat`-based solvers.
The patch implementing the second variant for `MiniSat` is displayed below.

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
our tool `sick-check` to verify incorrectness of the proof without doing any
unit propagation. Furthermore, the size of the incorrectness certificate is
in practice linear in the size of the formula, while proofs are exponential.

Let us give an  an example of a SICK certificate.  The first two columns show
a satisfiable formula in DIMACS format and an incorrect DRAT proof for this
formula.  The third column has the corresponding SICK certificate, stating
that the RAT check failed for the first lemma in the proof.  The certificate
file format is using TOML[^toml] syntax.

Formula     Proof   SICK Certificate
----------- ------- ---------------------------------------------
`p cnf 2 2` `1 0`   `proof_format   = "DRAT-arbitrary-pivot"`
`-1 -2 0`   `0`     `proof_step     = 1`
`-1 2 0`            `natural_model  = [-1, ]`
                    `[[witness]]`
                    `failing_clause = [-2, -1, ]`
                    `failing_model  = [2, ]`
                    `pivot          = 1`

Grammar
-------

```
SICK            := ProofFormat ProofStep NaturalModel Witness*
ProofFormat     := 'proof_format' '=' ( "DRAT-arbitrary-pivot"
                                      | "DRAT-pivot-is-first-literal")
ProofStep       := 'proof_step' '=' Integer
NaturalModel    := 'natural_model' '=' ListOfLiterals
Witness         := FailingClause FailingModel Pivot
FailingClause   := 'failing_clause' '=' ListOfLiterals
FailingModel    := 'failing_model' '=' ListOfLiterals
Pivot           := 'pivot' '=' Literal
ListOfLiterals  := '[' (Literal ',')* ']'
```

Explanation
-----------

- `proof_format` describes the proof format to use.
   - `DRAT-arbitrary-pivot`: DRAT checking where the pivot can be any literal
   in the lemma. This requires one witness (counter-example) for each possible
   pivot in the failing lemma. The pivot has to be specified for each witness.
   - `DRAT-pivot-is-first-literal`: Similar, but there is only one witness.
   The pivot needs to be the first literal in the lemma.
- `proof_step` specifies the proof step that failed, starting at one.
  For the remainder of this section, let the lemma denote the clause that is
  introduced by the referenced proof step.  In case of a textual proof this
  corresponds to the line number of the introduction instruction that failed.
- `natural_model` gives the partial model or trail before
  checking this proof step, obtained by exhaustively propagating units
  in the accumulated formula. This is included to avoid having to perform
  propagation in a checking tool.

Each witness is a counter-example to some redundancy check.

- `failing-clause`: A clause in the formula, which is a resolution candidate
  for the lemma.  This means that RUP of the resolvent on the pivot literal
  of the lemma and the failing clause.
- `failing-model`: The literals that were added to the natural model (trail)
  when performing the failed redundancy check.
- `pivot`: This specifies the pivot literal.

Note that if the lemma is the empty clause, no witness is needed.  This
corresponds to a proof containing an empty clause that cannot be derived by
unit propagation.

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
    3. $m_f$ contains the reverse units from the resolvent of the lemma and the failing clause.
    4. $m_f$ contains no clause that is unit under $m_f$ and not already in $m_f$.

Contribution
------------

Our contribution consists of adding support for proof format
`DRAT-arbitrary-pivot` which requires multiple witnesses, and the usage
of TOML.

6. Checker Implementation
=========================

The implementation (`rate`) is available [^rate].

Features
--------

- check DRAT proofs
- output core lemmas as DIMACS, LRAT or GRAT for accepted proofs
- output SICK certificate of unsatisfiability for rejected proofs
- competitive performance due to backwards checking with core-first unit
propagation
- option to ignore unit deletions, including reason deletions (flag `-d` or
`--skip-unit-deletions`)
- output several metrics regarding reason deletions
- decompress input files on-the-fly (Gzip, Zstandard, Bzip2, XZ, LZ4)

The debug build comes with lots of assertions, including checks for arithmetic
overflows and narrowing conversions that cause unintended changes of values.

Rust
----

We chose modern systems programming language Rust[^rust] for our
implementation.  Amongst the respondents of the 2019 Stackoverflow Developer
Survey[^so-survey] it is the most loved programming language and Rust
developers have the highest rate of contributing to open source projects.

Based on our successful implementation, we believe that, while there may be
some inconveniences with the borrow checker[^partial-ref], it is a viable
alternative to C and C++ for the domain of SAT solving.  The first serious
solver written in Rust, `varisat`[^varisat] is a great example of this.

Clause Identifiers
------------------

Other DRAT checkers use 30 bits to for unique clause identifiers.  We use
62 bits, mimicking a decision in `CaDiCaL`[^cadical-clauses].  This might
be disadvantageous in terms of performance and could be changed in future.

One problem with backards checking is that the LRAT proof has to be
stored in memory until the verification is complete. Since LRAT proofs
are even larger than DRAT proofs this can cause serious problems with
memory consumption[^sc18-results].  In order to make `rate` comparable to
`DRAT-trim` in terms of memory consumption, we also use 30 bits for clause
hints in the LRAT proof.

7. Experimental Evaluation
==========================

To evaluate our tool, we performed experiments, the detailed set-up is
available[^rate-experiments].

We work on proofs produced by solvers from the SAT competition 2018[^sc18].  As
described in [Section 4][4. Solvers], the proofs produced by `MiniSat`-derived
solvers are likely not meant to be interpreted as specified DRAT, so the
relevancy of our benchmarks is questionable.

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

-   We used the same limits as in the SAT competition --- 5000 seconds CPU
    time and 24 GB memory using runlim[^runlim]. For checking the timeout
    is 20000 seconds, which is also in line with the competition.

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
rejected under the semantics of specified DRAT. In our set of benchmarks
only around one third of the proofs were accepted by `rate` in the default
configuration, while all of them are accepted by `rate --skip-unit-deletions`.

As in [@RebolaCruz2018] we only compare the performance on proofs that
were accepted by all checkers, because a rejection makes the checker exit early.

- Please note that `rate -d` is equivalent to `rate --skip-unit-deletions`,
standing for the executions of `rate` checking operational DRAT.

- We present performance data as reported by `runlim` --- time in seconds
and memory usage in megabytes (2^20^ bytes).


Overall, the performance of the four checkers we analyze is very similar, as
can be seen by the boxplots for runtime (Figure @fig:box-time).  The memory
usage (Figure @fig:box-space) is higher in `rate`, likely due to to the
difference described in [Clause Identifiers], but there should be no
asymptotical difference.

![Boxplot of checker runtimes across all proofs](p/box-time.svg){#fig:box-time}

![Boxplot of the checkers' memory usage across all proofs](p/box-space.svg){#fig:box-space}


In figure @fig:cactus-time and @fig:cactus-space we show the distribution of
performances across the most difficult proof instances.  Those plot suggest
that `gratgen` is a bit faster, and `DRAT-trim` is slightly slower than
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

Figure @fig:correlation-reason-deletions-time-delta suggests that a large
number of reason deletions brings about some runtime overhead in `rate` when
checking specified DRAT as opposed to operational DRAT.  A significant overhead
in memory consumption occurs in only one instance, which also has a high number
of reason deletions, see figure @fig:correlation-reason-deletions-space-delta.

Note that this overhead also occurs for proofs that only contain redundant
reason deletions. For this class of proofs, the overhead could be easily
remedied with a small change to the checking algorithm.  However, it is not
yet clear to us how this should be done ideally.  Assuming solvers produced
proofs with (redundant) reason deletions only after addition of the unit
clause replacing other reason clauses, this would be trivial.  This class
of proofs is the one implemented by the second variant of the patches from
[section 4][4. Solvers].

8. Conclusion
=============

We have provided some evidence to our hypothesis that checking specified DRAT
is, on average, as expensive as checking operational DRAT, but an excessive
number of reason deletions can make it more costly.

We encourage SAT solver developers to to apply our patch to their
`MiniSat`-based solvers in order to create proofs that are correct under
either flavor and do not require the workaround of skipping reason deletions.

9. Future Work
==============

While our checker for specified DRAT is not really any more useful than one
for operational DRAT in terms of checking SAT solvers' unsatisfiability
results, it might be useful for checking inprocessing steps with reason
deletions Additionally it can be extended to support new proof formats.

If a checker for specified DRAT were to be adopted, it might be beneficial
to implement a way to handle redundant reason deletions more efficiently
than `rate` does, ideas for doing so are described in [Overhead of Reason
Deletions].

Current DRAT checkers are heavily optimized for speed but they keep the entire
input proof and the resulting LRAT certificate in memory. If the available
memory is at premium, some changes could be made to do backwards checking
as the proof instructions are read.  Additionally, the LRAT proof could be
output on-the-fly as well, with some postprocessing to fix the clause IDs.

It might be possible to forego DRAT completely and directly generate LRAT
in a solver which is done by `varisat`. This removes the need for a complex
checker at the cost of a larger proof artifact.


[^acl2]: <https://github.com/acl2/acl2/>
[^rupee]: <https://github.com/arpj-rebola/rupee>
[^rate]: <https://github.com/krobelus/rate>
[^sc18]: <http://sat2018.forsyte.tuwien.ac.at/>
[^sc18-results]: <http://sat2018.forsyte.tuwien.ac.at/results/main.csv>
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
[^so-survey]: <https://insights.stackoverflow.com/survey/2019>
[^rust]: <https://www.rust-lang.org/>
[^partial-ref]: <https://jix.one/introducing-partial_ref/>
[^cadical-clauses]: <https://github.com/arminbiere/cadical/blob/master/src/watch.hpp#L9>
[^reason-deletions-shrinking-trail]: The non-redundant reason deletions are
called `reason deletions shrinking trail` in the output of `rate`.

References
==========
