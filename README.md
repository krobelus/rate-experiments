---
author: Johannes Altmanninger
bibliography: references.bib
date: \today
csl: ieee.csl
link-citations: true
title: |
        DRAT Proofs without Non-Redundant Reason Clause Deletions 
            &
        Complete and Fast DRAT Proof-Checking
header-includes: |
        \usepackage{todonotes}
        \title{
            DRAT Proofs without Non-Redundant \\ Reason Clause Deletions \\
            \&\\
            Complete and Fast \\ DRAT Proof-Checking
        }
        \renewcommand{\title}[1]{}
---

::: {.abstract}
**Abstract:** Clausal proof format DRAT is the de facto standard way to certify
SAT solvers' unsatisfiability results.  State-of-the-art DRAT checkers ignore
deletions of unit clauses, which means that they are checking against a proof
system that differs from the specification of DRAT.  We demonstrate that it
is possible to implement a competitive checker that honors unit deletions.
Many reputable SAT solvers produce proofs that are incorrect under the DRAT
specification, because they contain spurious reason deletions. We present
patches for competitive SAT solvers to produce correct proofs with respect
to the specification.
:::

1. Introduction
===============

In past decades, there has been significant progress in SAT solving
technology. SAT solvers have had documented bugs [@BrummayerBiere-SMT09]
[@BrummayerLonsingBiere-SAT10].  To protect against these, there are
checker programs that verify a solver's result.  To do this, the solver
outputs a witness alongside its result. A checker program can reproduce the
solver's result using that witness. If the checker succeeds at doing so,
it *accepts* or *verifies* the witness.  Satisfiability witnesses, or models
are trivial to check in linear time.  Unsatisfiability witnesses, or proofs
of unsatisfiability on the other hand can be much more costly to check.
In SAT competitions, solvers are required to give proofs of unsatisfiability.
The proof format that is being used today is called *delete resolution
asymmetric tautology* (DRAT) [@Heule_2014].

A solver operates on a formula that acts as knowledge base.  It contains
constraints that are called clauses.  Starting from the input formula,
clauses are added and deleted during the process of solving.  A DRAT proof
is a trace of the solver's execution, containing information on which clauses
are added and deleted.

Deletions were introduced in solvers based on the *conflict-driven
clause-learning* (CDCL) architecture to increase their performance.  However,
in many proofs produced by current solvers there are some deletions of
reason clauses, yet these solvers do not actually undo assignments that were
caused by those clauses.  State-of-the-art proof checkers ignore deletions of
unit clauses (including reason clauses) and thus match the solvers internal
behavior.  As a result, the checkers are not faithful to the specification
of DRAT proofs [@rebola2018two].  We provide patches for top-performing
solvers to make them generate proofs without those spurious reason deletions.

We refer to the original definition of the proof format as *specified* DRAT
and to the one that is actually implemented by state-of-the-art checkers
as *operational* DRAT [@rebola2018two]. The classes of proofs accepted by
checkers of these two flavors of DRAT are incomparable.  Specified DRAT is
necessary to verify solvers' inprocessing steps which are employing reason
deletions [@rebola2018two].

DRAT proof-checking is computationally expensive, so it is desirable to
optimize checkers.  In theory, checking costs are comparable to solving
[@Heule_2014] Consider the problem of the Schur Number Five, where solving
took just over 14 CPU years whereas running the DRAT checker on the resulting
proof took 20.5 CPU years [@schur-5].  There exists an efficient algorithm
for specified DRAT [@RebolaCruz2018]. We provide an optimized implementation
which was missing.  Previous empirical results for that algorithm suggest
that the computational costs of checking DRAT is the almost the same for
either flavor of DRAT.

We have re-implemented the algorithm in combination with other optimizations
to roughly match the performance of the fastest checkers.  We provide more
extensive results, supporting that specified and operational DRAT are equally
expensive to check on an average real-world instance.  We also observe that
a high number of reason deletions tends to have a significant impact on
checking performance.

The majority of today's proofs are incorrect under specified DRAT.  In order
to find possible bugs in proof generation and proof-checking procedures, we
use the previously unpublished incorrectness certificate SICK.  It specifies
the format for a small witness that can be efficiently checked to verify
that a proof is indeed incorrect. We contribute a small modification to the
SICK format.

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
in the area of proof-checking.

2. Preliminaries
================

Notation
--------

A literal is a propositional variable, like $x$, or a negation of a variable,
denoted by $\overline{x}$. A clause is a disjunction of literals, usually
denoted by juxtaposition of the disjuncts, e.g. we write $xy\overline{z}$
for $x \lor y \lor \overline{z}$.

An assignment is a finite, complement-free set of literals. All literals in an
assignment are considered to be satisified by that assignment.  Conversely,
the complements of those literals are falsified by that assignment.  Other
literals are unassigned.  If there is some variable that is not assigned in
either polarity, then the assignment is partial.

SAT Solving
-----------

SAT solvers work on formulas in conjunctive normal form (CNF), conjunctions
of clauses.  A clause is satisfied by an assignment $I$ if any literal in the
clause is satisfied by $I$.  A formula in CNF is satisified by $I$ if each of
its clauses is satisfied by $I$.  An assignment that satisfies a formula is
called a model for that formula.  A formula is satisfiable if there exists
a model for it. Two formulas $F$ and $G$ are *satisfiability-equivalent*
if $F$ is satisfiable if and only $G$ is satisfiable.

A SAT solver takes as input a formula and finds a model if the formula
is satisfiable.  Otherwise, the solver provides a proof that the formula
is unsatisfiable.  This proof needs to derive the trivially unsatisfiable
empty clause.

While searching for a model, a solver maintains a partial assignment along
with the order in which the literals were assigned.  We call this data
structure the *trail*.

SAT solvers search through the space of all possible assignments.  They make
assumptions, adding literals to the trail that might be part of a satisfying
assignment.  At each step, unit propagation, which will be introduced
later, can add more literals to the trail, pruning assignments from the
search space that are definitely unsatisfiable. These literals are said to
be *forced*, because they, unlike assumptions, are necessarily satisfied in
any model based on the given assumptions --- that is, any model that is
a is a superset of the literals in the current trail.  If unit propagation
is performed on a trail without assumptions, the trail contains the set of
top-level forced literals which is a subset of any model.  Once the set of
top-level forced literals falsifies a clause, then the solver has derived
the empty clause and therefore established unsatisfiability of the current
formula and also the input formula.

Unit Propagation
----------------

\todo{split in naive UP, and efficient version with watches}

Given an assignment, a *unit clause* contains only falsified literals except
for a single non-falsified *unit literal*.

At any point during a solver's search, if the formula contains a unit clause
given the current assignment, the unit literal $l$ in that clause is forced
and added to the trail.  The unit clause is recorded as the *reason clause*
for $l$.  Everytime a literal $l$ is added to the trail, the formula will
be simplified by *propagating* $l$: any clause containing $l$ is discarded
because it will be satisfied by $l$, and occurrences of $\overline{l}$
are removed from the remaining clauses. The latter step may spawn new unit
clauses and thus trigger further propagation.

Note that there may be multiple potential reason clauses for some literal.
Therefore reason clauses are specific to a concrete propagation sequence in
a solver or checker.

As assumptions need to be undone during search, the implementation of unit
propagation does not actually delete clauses and literals, but merely scans the
formula for new units.  In order to efficiently keep track of which clauses
can become unit, competitve solvers and checkers use the two-watched-literal
scheme [@Moskewicz:2001:CEE:378239.379017]. It consists of a watchlist
for each literal in the formula, which is a list of clause references.
Clauses in the watchlist of some literal are said to be *watched on* that
literal.  Each clause is watched on two literals, which are also called its
*watches*. Provided that Invariant 1 from [@RebolaCruz2018] is maintained,
it suffices to look at the watches to determine that a clause is not unit.

**Invariant 1.** If a clause is watched on two distinct literals $l$ and $k$,
and the current trail $I$ falsifies $l$, then $I$ satisfies $k$.

In particular, when literal $l$ is assigned, it is propagated by scanning
the watchlist of $\overline{l}$, thus visiting only clauses that are watched
on $\overline{l}$. Since their watch $\overline{l}$ is falsified, Invariant
1 might need to be restored.

\if0 % implementation detail
Note that, as in [@RebolaCruz2018], clauses of size one are extended by a
single literal $\overline{\top}$ to make the manipulations of watches work
the same way for all clauses.
\fi

CDCL
----

Predominant SAT solvers implement Conflict Driven Clause Learning (CDCL).
Whenever a clause in the formula is falsified, this means that the current
set of assumptions can not be a subset of any model. Therefore a subset of
the assumptions is reverted and a *conflict clause* is learned, and added to
the formula to prevent the solver from revisiting those wrong assumptions.
As the number of clauses increases, so does memory usage, and the time spent
on unit propagation. Because of this, redundant (introduced in [Redundancy
Criteria]) learned clauses are regularly deleted from the formula if they
are not considered useful.

Redundancy Criteria
-------------------

A clause $C$ is redundant in formula $F$ if $F$ and $F \cup \{C\}$ are
satisfiability equivalent [@Heule_2017].

There are various criteria of redundancy, with different levels of expressivity
and computational costs.  Each lemma in a clausal proof must be redundant
according to the proof's redundancy criteria.

**Redundancy Criteria RUP:** a clause $C$ is RUP (reverse unit propagation)
in formula $F$ if unit propagation on $F' := F \cup \{ \{\overline{l}\}
\,|\, l \in C \}$ derives the empty clause.  A subsequence of clauses in
such a successful propagation sequence can then be used to derive $C$ using
the resolution rule, which means that $C$ is a logical consequence of $F$.
\todo{find a better way to explain soundness?} To compute whether some clause
is RUP, the negated literals in clause are added as assumptions and propagated.

**Redundancy Criteria RAT:** a clause $C$ is a *resolution asymmetric
tautology* (RAT) [@inprocessingrules] on some literal $l \in C$ with respect
to formula $F$ whenever for all clauses $D \in F$ where $\overline{l} \in D$,
the resolvent on $l$ of $C$ and $D$, which is $(C \setminus \{l\}) \cup (D
\setminus \{\overline{l}\})$ \todo{include $l$ in the resolvent?} is RUP in
$F$. Clause $D$ is called a *resolution candidate* for $C$. Computing whether
a clause is RAT can be done with one RUP check for each resolution candidate.

Clausal Proofs
--------------

A formula in CNF can be regarded as a multiset of clauses.  Each step in a
clausal proof adds a clause to the current formula, or deletes one from it.
These steps simulate the clause introductions and clause deletions that a
solver performs.  As a result, a checker can reproduce the solver's formula
as well as the set of top-level forced literals at each step, and finally
derive the empty clause just like the solver did.

\paragraph{Deletions} A proof solely consisting of clause introductions
will result in the checker's propagation routines slowing down due to
the huge number of clauses as described in [CDCL].  To counteract this,
clause deletion information has been added to proof formats, making the
proof-checking time comparable to solving time [@Heule_2014] [@Wetzler_2014].

DRAT Proofs
-----------

State-of-the-art SAT solvers use complex techniques to simplify the formula
before search and during with search --- termed preprocessing and inprocessing
respectively.  Proofs based on RUP alone are not expressive enough to
simulate all preprocessing and inprocessing techniques in modern SAT solvers
[@rat]. For this reason, the more powerful criteria RAT is used today [@rat].

A DRAT (*delete resolution asymmetric tautology*) proof is a clausal proof
with deletions where every lemma is RUP or RAT.  In practice, most lemmas
are RUP, so a checker first tries to check RUP and only if that fails,
falls back to RAT.

While deletions were added to proofs to optimize checking runtime, they
can also be enable additional inferences due to RAT being non-monotonic
[@philipp_rebola_unsatproofs].

As in [@rebola2018two], we refer to *operational DRAT* as the flavor of DRAT
where deletions of unit clauses are ignored, as opposed to *specified DRAT*.

LRAT Proofs
-----------

The runtime and memory usage of DRAT checkers can exceed the ones of the
solver that produced the proof. The resulting need for a DRAT checker to be as
efficient as possible makes it difficult to implement a mechanically verified
checker. This is remedied by making the DRAT checker output an optimized (i.\
e.\ small) and annotated proof in LRAT format [@cruz2017efficient]. Checking
this proof does not require propagation and there are verified implementations
available[^acl2].

An LRAT proof is a clausal proof just like DRAT, but it includes clause hints
for each resolution candidates and all unit clauses that are necessary to
derive a the empty clause to show that the resolvent is a RUP.

Backwards Checking
------------------

The naïve way to verify that a proof is correct consists of performing
each instruction in the proof from the first to one last one, while checking
each lemma.

During search, SAT solvers cannot know which learned clauses are useful in a
proof, so they simply add all of them as lemmas. This means that many lemmas
might not be necessary in a proof of unsatisfiability.  To avoid checking
superfluous lemmas, the proof is checked backwards --- starting from the
empty clause, only lemmas that are transitively necessary to derive that
empty clause are checked [@Heule_2013].

This can be done using two passes over the proof: a forward pass performing
unit propagation [@RebolaCruz2018] until the empty clause is derived, and
a backward pass that actually checks lemmas as required.

Thinking of formulas as sets of clauses, an *unsatisfiable core*, for short
*core* is an unsatisfiable subset of an unsatisfiable formula. With backwards
checking, a core is eventually computed and only core lemmas are checked.
Whenever the empty clause is derived as part of some redundancy check,
conflict analysis adds to the core all clauses that were required to do so.
This is done by a depth-first search in the graph induced by the reason
clauses: starting from the clause that was falsified, the clause is added
to the core and, for each of its literals $l$, the same is done recursively
for the reason for $\overline{l}$.

A by-product of this core computation is a *trimmed proof*, consisting of all
core lemmas. The LRAT output is the trimmed proof supplemented by clause hints.

Checking a lemma requires finding one or more conflicts via unit propagation.
The trail is a mutable data structure that maintains the set of top-level
forced literals as well as literals assigned due to assumptions.  After adding
or deleting a clause, the trail is modified accordingly which is arguably
more efficient than computing it from scratch.  In the forward pass, an
introduction instruction may cause propagation and a deletion instruction
may cause some literals to be removed from the trail.  On the other hand the
backward pass traverses the proof in reverse order and executes the inverse
of each proof step, that is, a clause introduction in the backward pass
deletes that clause from the formula while a clause deletion in the backward
pass re-introduces the deleted clause. The trail is modified, reverting the
modification done in the forward pass.  This ensures that when processing
some lemma the trail is the same during forward and backward pass.


Core-first Unit Propagation
---------------------------

In order to keep the core small and reduce checking costs, core-first unit
propagation was introduced [@Heule_2013].  It works by doing unit propagation
in two phases:

1. Propagate using clauses already in the core.
2. Examine non-core clauses:
   - If there is some unit clause with an unassigned unit literal, propagate
   that and go to 1.
   - Otherwise terminate.

This results in a local minimum of clauses being added to the core.

Reason Deletions
----------------

As explained in [@RebolaCruz2018], when checking a proof without deletions of
reason clauses, the trail grows monotonically, that is, it never shrinks at any
proof step during the forward phase. Therefore, during the backwards phase it
is trivial to revert the modifications to the trail by simply truncating it.
This also maintains watch invariants, making sure that the watchlists can
find all unit clauses.

However, when a proof with reason deletions is checked under specified DRAT,
the algorithm from [@RebolaCruz2018] is required to restore Invariant 1 in
the backward pass. While an understanding of the algorithm is not required
to understand the contributions in this paper, we explain parts of it nevertheless.

Let us consider a proof with reason deletions.  A deletion instruction is
performed by removing a clause from the formula in the forward pass and
re-introducing it in the backward pass.  This is implemented by removing the
clause from the watchlists and adding it respectively.

During the forward pass, whenever the reason clause for some literal is
deleted, this literal is unassigned.  If it was used to propagate some other
unit, that one may be unassigned as well, and so on. All these literals
form the *cone of influence* (see [@RebolaCruz2018]) of the first literal
and are recorded in the checker, alongside their positions in the trail,
and reasons clauses. This allows the checker to re-introduce the literals
from the cone later in the backward pass when the deletion is undone.

\if0
The recorded information can then be used in the backward pass to patch the
trail at the reason deletions in order for the trail to be exactly as it
was during the forward phase. The tricky part here is to correctly restore
the Invariant 1 in all affected clauses.
\fi

When a reason deletion is processed during the backwards phase, each
literal in the cone will be reintroduced into the trail at the recorded
position.  Consider literal $l$ in the cone. Before applying the backwards
deletion $l$ could have been satisfied or unassigned (but not falsified).
After reintroducing $l$, it is satisfied. Therefore, a clause containing
$\overline{l}$ might become unit without the checker noticing.  Because of
this, the watchlists of all reverse cone literals $\overline{l}$ have to be
traversed to restore the watch invariant.  Each of those clause is watched
on falsified literal $\overline{l}$. Therefore the watches may need to be
replaced in order to restore Invariant 1.

If above clause has at least two non-falsified literals, the watches can be set
to any two out of those.  However, if the clause has only one non-falsified
literal --- which is necessarily satisifed because of Invariant 1 --- then
the other watch cannot be choosen arbitrarily because this might provoke a
violation of Invariant 1 at a later point as described in [@RebolaCruz2018;
Example 5].  The second watch may be set to the most recently falsified
literal $l_r$, or any other literal that was falsified during the propagation
that was done after adding the lemma that resulted in the propagation of $l_r$.

Existing Checkers
-----------------

We heavily draw upon existing checkers. In fact, our implementation contains
no algorithmic novelties but merely combines the ideas present in existing
checkers.

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
which may explain parts of the difference in performance.

Additionally `rupee` does not use core-first unit propagation while the
other checkers do.

3. Two Kinds of Reason Deletions
=============================

Here we clarify which reason deletions are actually problematic.

In general, deleting a reason clause shrinks the trail.  However, if, and
only if there is another clause that can act as reason for the same literal
at any point during unit propagation, then the set of literals in the trail
does not change.  We call this special case a *redundant reason deletion*,
and the other case a *non-redundant reason deletion*.

Note that the term *unit deletion* comprises deletions of any unit clause,
that is, reason deletions and other deleted units that were not propagating.
State-of-the-art checkers ignore unit deletions.

A proof of unsatisfiability generated by a SAT solver should not contain
any non-redundant reason deletions.  Other current checkers can report unit
deletions and reason deletions but they do not distinguish between redundant
and non-redundant reason deletions.  Our tool also outputs the number of
non-redundant reason deletions [^reason-deletions-shrinking-trail]. This
might be useful to sanity-check SAT solvers' proof generation procedures.

Given a proof without non-redundant reason deletions, checkers for
*operational* and *specified* DRAT behave exactly the same way.

Due to different propagation orders, a clause that is a reason in the solver
might not be in the checker and vice versa.  This happens if there exist
two propagation orders such that a clause $C$ is a reason in one but not
in the other. When deleting a non-redundant reason $C$, there exists no
other reason for the propagated literal, and therefore $C$ is a reason in
any propagation order.

\if0
The takeaway here is that the different propagation
orders in solver and checker do not matter, because non-redundant reasons
are always reasons in both solver and checker. On the other hand, deletions
of clauses that are a reason in one but not the other are always redundant
and do not influence the trail, so it actually does not matter whether they
are a reason in the checker or not.
\fi
\if0
State-of-the-art checkers ignore deletions of reason clauses,
including clauses that were not reasons in the solver.
However, since deletions of the latter do not shrink the trail,
\fi
\if0
Due to different propagation orders, a clause that is a reason in the solver
might not be in the checker and vice versa.  This happens if there exist
two propagation orders such that a clause $C$ is a reason in one but not in
the other.  In particular, if $C$ is a reason in a checker, then a deletion
of $C$ is a redundant reason deletion since there exists a propagation order
with a different reason for the propagated literal.
\fi


4. Solvers
==========

In this section we take a look at why the discrepant proofs are produced in
the first place, and present patches to make solvers generate proofs without
non-redundant reason deletions.

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
`-1  2 0`            `natural_model  = [-1, ]`
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
5. For format `DRAT-arbitrary-pivot`, all pivots are specified and precisely
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
alternative to C and C++ for the domain of SAT solving. The first Rust-based
solver to take part in competitions `varisat`[^varisat] is a great example
of this.

Clause Identifiers
------------------

Other DRAT checkers use 30 bits to for unique clause identifiers.  We use
62 bits, mimicking a decision in `CaDiCaL`[^cadical-clauses].  This might
be disadvantageous in terms of performance and could be changed in future.

One problem with backwards checking is that the LRAT proof has to be
kept in memory until the verification is complete. Since LRAT proofs are
even larger than DRAT proofs this can cause serious problems with memory
consumption[^sc18-results].  In order to make `rate` comparable to `DRAT-trim`
in terms of memory consumption, we also use 30 bits for clause hints in the
LRAT proof.

7. Experimental Evaluation
==========================

To evaluate our tool, we performed experiments, the detailed set-up is
available[^rate-experiments].

We work on proofs produced by solvers from the SAT competition 2018[^sc18].  As
described in [Section 4][4. Solvers], the proofs produced by `MiniSat`-derived
solvers are probably not meant to be interpreted as specified DRAT, so the
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
same distribution of runtimes.

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
[^reason-deletions-shrinking-trail]: The metric for the number of non-redundant
reason deletions is called `reason deletions shrinking trail` in the output of
`rate`.

References
==========
