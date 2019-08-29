---
author: Johannes Altmanninger
bibliography: references.bib
date: \today
csl: ieee.csl
link-citations: true
documentclass: report
title: |
        DRAT Proofs Without Deletions of Unique Reason Clauses 
            &
        Complete and Fast DRAT Proof-Checking
header-includes: |
        \usepackage{todonotes}
        \title{
            DRAT Proofs Without Deletions of \\ Unique Reason Clauses \\
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
specification, because they contain spurious deletions of reason
clauses. We present patches for top SAT solvers to produce correct proofs
with respect to the specification.
\todo{sick, results}
:::

\tableofcontents

1. Introduction
===============

Over past decades, there has been significant progress in SAT solving
technology. SAT solvers have had documented bugs [@BrummayerBiere-SMT09]
[@BrummayerLonsingBiere-SAT10].  As a measure to detect incorrect results,
there are *checker* programs that *verify* a solver's result based on a witness
given by the solver. Satisfiability witnesses, or models are trivial to check
in linear time.  Unsatisfiability witnesses, or proofs of unsatisfiability
on the other hand can be much more costly to check.

A SAT solver operates on a formula that acts as knowledge base.  It contains
constraints that are called clauses.  Starting from the input formula,
clauses are added and deleted by the solver.  In SAT competitions, solvers
are required to give proofs of unsatisfiability in the DRAT proof format
[@Heule_2014]. A DRAT proof is a trace of a solver execution, containing
information on which clauses are added and deleted.

Deletions were introduced in solvers based on the *conflict-driven
clause-learning* (CDCL) architecture to improve performance [@cdcl].  Many
state-of-the-art CDCL solvers emit deletions of reason clauses, yet
these solvers do not undo inferences made using those clauses.  Perhaps because
of this inconsistency, state-of-the-art proof checkers ignore deletions of
unit clauses [@rebola2018two] (including reason clauses), matching the
solvers' internal behavior.  As a result, the checkers are not faithful to
the specification of DRAT proofs [@rebola2018two].  We provide patches for
award-winning solvers to make them generate proofs without those spurious
deletions of reasons, eliminating the need to ignore some deletion
instructions.\todo{xx}

We refer to the original definition of the proof format as *specified* DRAT and
to the one that is implemented by state-of-the-art checkers as *operational*
DRAT [@rebola2018two]. The classes of proofs verified by checkers of these
two flavors of DRAT are incomparable.

State-of-the-art SAT solvers use complex inprocessing techniques to modify
a formula. When DRAT proof logging is desired, such a modification needs to
be expressed by some lemmas and clause deletions.  If these use deletions
of reason clauses then a checker for specified DRAT is necessary to verify
the inprocessing step [@rebola2018two] because a checker for operational
DRAT would ignore the deletions which can cause future correct proof steps
to be rejected.  The absence of an efficient checker for specified DRAT
means that solvers cannot use such techniques in competitions. We provide
the first optimized checker for specified DRAT.

DRAT proofs are designed to use minimal space for each lemma but checking them
is computationally expensive.  In theory, checking costs are comparable to
solving [@Heule_2014]. Consider the problem of the Schur Number Five, where
solving took just over 14 CPU years whereas running the DRAT checker on the
resulting proof took 20.5 CPU years [@schur-5].  We implemented an algorithm
that was published in [@RebolaCruz2018] to efficiently check specified DRAT.
Previous empirical results for that algorithm suggest that the computational
costs of checking DRAT are practically the same for both flavors of DRAT
but those results were produced with a checker that was not competitive in
terms of performance.  Our implementation has state-of-the-art performance.
We provide more extensive results, providing more evidence that specified and
operational DRAT are equally expensive to check on the average real-world
instance.  We also observe that a high number of reason deletions tends to
have a significant impact on checking performance.\todo{xx}

The majority of solvers at SAT competitions produce proofs that are
incorrect under specified DRAT. For those proofs, our checker outputs a
small, efficiently checkable incorrectness certificate in the SICK format
which was originally developed for the first checker for specified DRAT but
not yet published.  The incorrectness certificate can be used to check the
incorrectness of a proof independently of the checker, which helps developers
debug proof-generation and proof-checking algorithms.  While checking
operational DRAT efficiently is arguably easier than specified DRAT, the
straighforward semantics of specified DRAT facilitates reasoning about a
proof, e.g.\ it allows the definition of the SICK format to be much simpler.
We contribute an extension to the SICK format.

This thesis is organized as follows: In [the following
section][2. Preliminaries] we will introduce preliminary knowledge about
SAT solving, proofs of unsatisfiability and proof checking, including the
challenges of specified DRAT checking of proofs containing reason deletions.
Our first contribution, a proposal on how to change solvers to produce
unambiguously correct proofs, can be found in [Section 3][3. DRAT Proofs
without Deletions of Unique Reason Clauses].  [Section 4][4. Complete and Fast
DRAT Proof-Checking] concerns the efficient implementation of a specified
DRAT checker:  after briefly discussing other checkers we present our
implementation and describe the SICK format for incorrectness certificates.
Experimental results evaluating checker performance are given in [Section
5][5. Experimental Evaluation].  Finally, we draw a conclusion in [Section
6][6. Conclusion] and give outlook on future work in the area of DRAT
proof-checking in [the last section][7. Future Work].

\todo{structure: present setting, research questions, contributions, roadmap}

2. Preliminaries
================

A *literal* is a propositional variable, like $x$, or a negation of a variable,
denoted by $\overline{x}$. A *clause* is a disjunction of literals, usually
denoted by juxtaposition of the disjuncts, e.g. we write $xy\overline{z}$
for $x \lor y \lor \overline{z}$.

An *assignment* is a finite, complement-free set of literals. All literals
in an assignment are considered to be *satisfied* by that assignment.
Conversely, the complements of those literals are *falsified* by that
assignment.  Other literals are *unassigned*.

SAT solvers work on formulas in *conjunctive normal form* (CNF), conjunctions
of clauses. A clause is satisfied by an assignment $I$ if any literal in the
clause is satisfied by $I$. A formula in CNF is satisfied by $I$ if each of
its clauses is satisfied by $I$. An assignment that satisfies a formula is
called a *model* for that formula. A formula is *satisfiable* if there exists
a model for it. Two formulas $F$ and $G$ are *satisfiability-equivalent*
if $F$ is satisfiable if and only $G$ is satisfiable.

2.1 SAT Solving
---------------

A SAT solver takes as input a formula and finds a model if the formula is
satisfiable. Otherwise, the solver provides a proof that the formula is
unsatisfiable. This proof needs to derive the unsatisfiable empty clause.

While searching for a model, a solver maintains an assignment along with
the order in which the literals were assigned.  We call this data structure the
*trail*.  SAT solvers search through the space of all possible assignments.
They make assumptions, adding literals to the trail that might be part
of a satisfying assignment.  At each step, unit propagation, which will
be introduced later, may add more literals to the trail.  These literals
are logically implied by the formula plus assumptions, assignments that
falsify them are pruned from the search space.  Once the trail falsifies a
clause, the solver has derived the empty clause and therefore established
unsatisfiability of the current formula and also the input formula.

\paragraph{Unit Propagation} Given an assignment, a *unit clause* contains
only falsified literals except for a single non-falsified *unit literal*.
At any point during a solver's search, if the formula contains a unit
clause given the current assignment, the unit literal $l$ in that clause is
necessarily satisfied and therefore added to the trail.  The unit clause
is recorded as the *reason clause* for $l$.  Every time a literal $l$ is
added to the trail, the formula will be simplified by *propagating* $l$:
any clause containing $l$ is discarded because it will be satisfied by $l$,
and occurrences of $\overline{l}$ are removed from the remaining clauses. The
latter step may spawn new unit clauses and thus trigger further propagation.

The *shared UP-model* is the assignment consisting of all literals implied by
unit propagation [@rebola2018two] in the current formula plus assumptions.

Given a formula where above unit propagation has been performed until fixpoint,
we call a unit clause $C$ with unit literal $l \in C$ a *unique reason clause*
if it was required to propagate $l$ in a formula --- that is, there can be
no other reason clause for $l$ when performing the propagations. Hence a
unique reason clause is defined with respect to a formula only, independent
of a propagation sequence. Every reason clause is a unit clause.

As assumptions need to be undone during search, the implementation of unit
propagation does not delete clauses and literals from the data structure,
but merely scans the formula for new units.  To efficiently keep track
of which clauses can become unit, competitive solvers and checkers use
the two-watched-literal scheme [@Moskewicz:2001:CEE:378239.379017]. It
consists of a watchlist for each literal in the formula, which is a list of
clause references.  Clauses in the watchlist of some literal are said to be
*watched on* that literal.  Each clause is watched on two literals, which are
also called its *watches*. Provided that Invariant 1 from [@RebolaCruz2018]
is maintained, it suffices to look at the watches to determine that a clause
is not unit.

**Invariant 1.** If a clause is watched on two distinct literals $l$ and $k$,
and the current trail $I$ falsifies $l$, then $I$ satisfies $k$.

In particular, when literal $l$ is assigned, it is propagated by scanning
the watchlist of $\overline{l}$, thus visiting only clauses that are watched
on $\overline{l}$. Since their watch $\overline{l}$ is falsified, Invariant
1 might need to be restored.

\paragraph{CDCL} Predominant SAT solvers implement Conflict Driven Clause
Learning (CDCL) which is based on the following principle: whenever some
clause in the formula is falsified under the current assignment, this means
that the current set of assumptions cannot be a subset of any model. Therefore
a subset of the assumptions is reverted and a *conflict clause* is learned
--- it is added to the formula to prevent the solver from revisiting those
wrong assumptions.  As the number of clauses increases, so does memory usage,
and the time spent on unit propagation. Because of this learned clauses are
regularly deleted from the formula in a satisfiability-preserving way if
they are not considered useful.

2.2 Proofs of SAT Solvers' Unsatisfiability Results
---------------------------------------------------

\paragraph{Redundancy Criteria} A clause $C$ is redundant in a formula
$F$ if $F$ and $F \cup \{C\}$ are satisfiability equivalent [@Heule_2017].
There are various criteria of redundancy, with different levels of expressivity
and computational costs.

1. *RUP*: a clause $C$ is RUP (reverse unit propagation) in formula $F$ if
unit propagation on $F' := F \cup \{ \overline{l} \,|\, l \in C \}$ derives
the empty clause [@rup]. To compute whether $C$ is RUP, the negated literals in
$C$ are added as assumptions and propagated until the empty clause is derived.
A clause that is RUP $F$ is logical consequence of $F$ [@rup].

2. *RAT* a clause $C$ is a *resolution asymmetric tautology* (RAT)
[@inprocessingrules] on some literal $l \in C$ with respect to formula $F$
whenever for all clauses $D \in F$ where $\overline{l} \in D$, the resolvent
on $l$ of $C$ and $D$, which is $(C \setminus \{l\}) \cup (D \setminus
\{\overline{l}\})$ is RUP in $F$. Clause $D$ is called a *resolution candidate*
for $C$. Computing whether a clause is RAT can be done with one RUP check
for each resolution candidate.


\paragraph{DRAT Proofs} Proofs based on RUP alone are not expressive enough
to simulate all inprocessing techniques in state-of-the-art SAT solvers
[@rat]. Because of this, the more powerful criterion RAT is used today [@rat].
A formula in CNF can be regarded as a multiset of clauses.  A DRAT (*delete
resolution asymmetric tautology*) [@Wetzler_2014] proof is a sequence of lemmas
(clause introductions) and deletions, which can be performed on a formula to
simulate the clause introductions, clause deletions and inprocessing steps
that the solver performed. The *accumulated formula* at each proof step is the
input formula with all clause introductions and deletions from prior proof
steps applied.  Based on the accumulated formula, the checker can compute
the shared UP-model at each step, eventually deriving the empty clause just
like the solver did. Every lemma in a correct DRAT proof is RUP or RAT with
respect to the accumulated formula.  In practice, most lemmas are RUP, so
a checker first tries to check RUP and only if that fails, falls back to RAT.

A proof solely consisting of clause introductions will result in the checker's
propagation routines slowing down due to the huge number of clauses just like
in a CDCL solver that does not delete learned clauses.  To counteract this,
clause deletion information has been added, making the proof-checking time
comparable to solving time [@Heule_2014] [@Wetzler_2014].  While deletions
were added as an optimization, they can also enable additional inferences
due to RAT being non-monotonic [@philipp_rebola_unsatproofs].

As in [@rebola2018two], we refer to *operational DRAT* as the flavor of DRAT
where deletions of unit clauses are ignored, as opposed to *specified DRAT*.

\paragraph{LRAT Proofs} The runtime and memory usage of DRAT checkers
can exceed the ones of the solver that produced the proof [@schur-5]. The
resulting need for a DRAT checker to be as efficient as possible requires
using mutable data structures that rely on pointer indirection which are
difficult to formally verify.  The lack of a formally verified DRAT checker
is remedied by making the DRAT checker output an annotated proof in the LRAT
format [@cruz2017efficient]. The LRAT proof can be checked by a formally
verified checker[^acl2] without unit propagation, making sure that the
formula formula is indeed unsatisfiable.  Most solvers can only generate
an DRAT proofs but DRAT checkers can be used to produce an LRAT proof from
a DRAT proof. The LRAT proof resembles DRAT, but it includes clause hints
for each resolution candidates and all unit clauses that are necessary to
derive the empty clause to show that each resolvent is a RUP.

2.3 Proof Checking
------------------

The naïve way to verify that a proof is correct consists of performing
each instruction in the proof from the first to the last one, while checking
each lemma.

\paragraph{Backwards Checking} During search, SAT solvers cannot know which
learned clauses are useful in a proof, so they add all of them as lemmas. This
means that many lemmas might not be necessary in a proof of unsatisfiability.
To avoid checking superfluous lemmas, the proof is checked backwards ---
starting from the empty clause, only lemmas that are transitively necessary
to derive that empty clause are checked [@Heule_2013].

This can be done using two passes over the proof: a forward pass performing
unit propagation [@RebolaCruz2018] until the empty clause is derived, and
a backward pass that checks lemmas as required.

A formula in CNF can be regarded as a multiset of clauses.  An *unsatisfiable
core*, for short *core* is an unsatisfiable subset of an unsatisfiable
formula. With backwards checking, a core is eventually computed like this:
whenever the empty clause is derived as part of some redundancy check,
conflict analysis adds to the core all clauses that were required to do so.
This is done through a depth-first search in the graph induced by the reason
clauses: starting from the clause that was falsified, the clause is added
to the core and, for each of its literals $l$, the same is done recursively
for the reason for $\overline{l}$.

Starting from the empty clause that finishes the proof, only lemmas that are
already in the core are checked. Other clauses and lemmas do not influence the
unsatisfiability result and are virtually dropped from the proof.  Tools like
`drat-trim` can output a *trimmed* proof that only contains core lemmas in
DRAT or LRAT format.

\if0
Checking a lemma requires finding one or more conflicts via unit propagation.
\fi

The trail is a mutable data structure that corresponds to the shared UP-model
of the accumulated formula at each proof step.  After adding or deleting a
clause, the shared UP-model changes and the trail is modified accordingly: In
the forward pass, an introduction instruction may cause the shared UP-model
to grow due to new propagation, while a deletion instruction may cause the
shared UP-model to shrink which means that some literals will be removed from
the trail.  Doing this modification is arguably more efficient than computing
the shared UP-model from scratch.  On the other hand, the backward pass
traverses the proof in reverse order and executes the inverse of each proof
step, that is, a clause introduction in the backward pass deletes that clause
from the formula, while a clause deletion in the backward pass re-introduces
the deleted clause. To make the trail correspond to the shared UP-model, in
the backward pass before each proof step the modification that was done in
the forward pass after this step needs to be reverted.  This ensures that when
some lemma is processed the trail is the same during forward and backward pass.

\paragraph{Core-first Unit Propagation} To keep the core small and reduce
checking costs, core-first unit propagation was introduced [@Heule_2013].
It works by doing unit propagation in two phases:

1. Propagate using clauses already in the core.
2. Examine non-core clauses:
   - If there is some unit clause with an unassigned unit literal, propagate
   that and go to 1.
   - Otherwise terminate.

This results in a minimum of clauses being added to the core because if a
conflict can be reached without adding another clause to the core it will
always do that. Overall, this usually seems to make checking faster, probably
because unit propagation is mostly done in the core instead of all clauses.

\paragraph{Reason Deletions} Here we explain, how reason deletions are
performed efficiently under specified DRAT. Unique reason deletions are
the cause for the discrepancy between specified and operational DRAT and
can in some cases be avoided as we will see in the next section. However,
to reliably detect unique reason deletions, it is necessary to implement
specified DRAT, as it is to support inprocessing steps with reason deletions.

As explained in [@RebolaCruz2018], when checking a proof without deletions
of unique reason clauses, the trail grows monotonically, that is, it never
shrinks at any proof step during the forward phase. Therefore, during the
backwards phase it is trivial to revert the modifications to the trail by
truncating it.  This also maintains watch invariants, making sure that the
watchlists can find all unit clauses.  However, when deleting a unique reason
clause in the forward pass under specified DRAT, some literals are removed from
the trail and reordered.  This means that it is not possible anymore to revert
this modification of the trail in the backward pass by truncating the trail.
Instead algorithm from [@RebolaCruz2018] can be used to restore the trail
and to efficiently reinstate the watchlists' Invariant 1 in the backward
pass. While an understanding of the algorithm is not required to understand
the contributions in this paper, we explain parts of it nevertheless.

Let us consider a proof with deletions of unique reasons.  A deletion
instruction is performed by removing a clause from the formula in the forward
pass and re-introducing it in the backward pass.  This is implemented by
removing the clause from the watchlists and adding it respectively.

During the forward pass, whenever the reason clause for some literal is
deleted, this literal is unassigned.  If it was used to make a clause unit
and thus propagate it, that unit may be unassigned as well, and so on. All
these literals form the *cone of influence* (see [@RebolaCruz2018]) of
the first literal. Before being unassigned, the literals in the cone are
recorded in the checker, alongside their positions in the trail and their
reason clauses. This information allows the checker to re-introduce the cone
literals later in the backward pass when the deletion is undone.

When the deletion of a reason is processed during the backwards phase, each
literal in the cone will be reintroduced into the trail at the recorded
position.  Consider literal $l$ in the cone. Before applying the backwards
deletion $l$ could have been satisfied or unassigned (but not falsified).
After reintroducing $l$, it is satisfied. Therefore, a clause containing
$\overline{l}$ might become unit without the checker noticing.  Because of
this, the watchlists of all reverse cone literals $\overline{l}$ have to be
traversed to restore the watch invariant.  Each of those clause is watched
on the now-falsified literal $\overline{l}$. Therefore the watches may need
to be replaced to restore Invariant 1.

If above clause has at least two non-falsified literals, the watches can be
set to any two out of those.  However, if the clause has only one non-falsified
literal --- which is necessarily satisfied because of Invariant 1 --- then the
other watch cannot be chosen arbitrarily because this might provoke a violation
of Invariant 1 at a later point as described in [@RebolaCruz2018; Example 5].
Instead, the second watch may be set to the most recently falsified literal
$l_r$, or any other literal that was falsified during the propagation that
was done after adding the lemma that resulted in the propagation of $l_r$.

3. DRAT Proofs without Deletions of Unique Reason Clauses
=========================================================

Operational DRAT (as opposed to specified DRAT) checking is currently used
to verify some solvers' proofs because these solvers emit unique reason
deletions. Since these solvers act as if reason clauses were not deleted
we propose patches to avoid deletions of unique reason clauses, matching
the solver's internal behavior.  Since for the fragment of proofs without
unique reason deletions, *operational* and *specified* DRAT coincide, these
proofs can then be checked with a checker of either flavor.

Out of the solvers submitted to the main track of the 2018 SAT competition,
the ones based on `MiniSat` and `CryptoMiniSat` produce proofs with deletions
of unique reasons while, to the best of our knowledge others do not.

Let us explain how `DRUPMiniSat`[^drupminisat] emits unique reason deletions.
Used during the simplification phase, the method `Solver::removeSatisfied`
looks for clauses that are satisfied by the shared UP-model and removes them
from the clause database and adds them as a deletion to the DRAT proof output.
Those clauses remain satisfied indefinitely for the rest of the search,
because the shared UP-model is a subset of any model.

In `MiniSat`, *locked* clauses are reasons for some literal in the trail.
The function `Solver::removeSatisfied` also deletes locked clauses, however,
the induced assignments are not undone.  This suggests that a locked clause is
implicitly kept in the formula, even though it is deleted.  State-of-the-art
DRAT checkers ignore deletions of unit clauses, which means they do not undo
any assignments when deleting clauses, matching the solvers' behavior.

We suggest two possible changes to make `DRUPMiniSat` produce proofs that
do not require this workaround of ignoring unit deletions when checking.

1. Do not remove locked clauses during simplification.

2. Before to removing locked clauses, emit the corresponding propagated
literal as addition of a unit clause in the DRAT proof.  Suggested by
Mate Soos[^suggestion-add-units], this option is also the preferred one
to the authors of `mergesat`[^mergesat-pr] and `varisat`[^varisat-pr].
Additionally, this is implemented in `CaDiCaL's`[^cadical] preprocessor.

The second variant does not influence of future inferences because the unit
clause that is added and the reason clause that is removed are equivalent
under the shared UP-model, whose literals will never be unassigned throughout
the solver's runtime.

\if0
Let us briefly explain why the second variant does not affect correctness
of future RAT inferences. Given the accumulated formula $F$, let some locked
clause $D \in F$ have satisfied literal $l \in D$ --- all other literals in
$D$ are falsified.  In the unpatched version, $D$ could be deleted.  Variant 1
prevents this by not deleting $D$ while variant 2 modifies the formula to be
$F' := (F \cup \{l\}) \setminus \{D\}$.  A clause $C$ is RAT in $F$ if and
only it is RAT in $F'$ because resolving $C$ with either $D$ or $l$ yields
two resolvents that are equivalent given the assignment of the shared UP-model.
\fi

We provide patches implementing these for `MiniSat` version 2.2
(1.  [^patch-MiniSat-keep-locked-clauses] and 2.[^patch-MiniSat]),
and the winner of the main track of the 2018 SAT competition
(1.[^patch-MapleLCMDistChronoBT-keep-locked-clauses] and
2.[^patch-MapleLCMDistChronoBT]).
Both patches are arguably rather simple and we do not expect any significant
impacts in terms of solver runtime, memory usage or proof size.  The same
methods can be applied easily to other `DRUPMiniSat`-based solvers.

4. Complete and Fast DRAT Proof-Checking
========================================

In this section, we discuss our implementation of a DRAT proof checker
after introducing existing checkers.  Finally we describe the format for
SICK witnesses which can be produced by our checker to give information on
why a proof was rejected.

4.1 Existing Checkers
---------------------

We heavily draw upon existing checkers. In fact, our implementation contains
no algorithmic novelties but merely combines the ideas present in existing
checkers.

\paragraph{\texttt{DRAT-trim}} The seminal reference implementation; Marijn
Heule's `DRAT-trim` can produce a trimmed proof in the DRAT or LRAT format. We
mimic their way of producing LRAT proofs and ensure that all our proofs are
verified by the formally verified checker[^acl2].  This gives us confidence
in the correctness of our implementation and allows for a comparison of our
checker with `DRAT-trim` since both have the same input and output formats.

`DRAT-trim` pioneered deletions, backwards checking add core-first propagation.
Additionally it employs an optimization to which we also use: during RAT
checks, resolution candidates that are not in the core are ignored, because
the proof can be rewritten to delete them immediately after the current
lemma[^gratgen-noncore-rat-candidates].

\paragraph{GRAT Toolchain} More recently, Peter Lammich has published the
GRAT toolchain [@lammich2017grat] that is able to outperform `DRAT-trim`
[@lammich2017efficient].

They first produce a GRAT proof which is (similar to LRAT) with the `gratgen`
tool, after which formally verified `gratchk` can be used to check the
certificate, guaranteeing that the original formula is indeed unsatisfiable.
We also implement GRAT generation in our tool. However, the `gratchk` tool
ignores unit deletions, so GRAT proofs are only useful for operational DRAT.

They introduce two notable optimizations:

1. Separate watchlists for core and non-core clauses[^gratgen-cf]. This
   speeds up unit propagation, so we use it in our implementation.

2. Resolution candidate caching / RAT run heuristic [@lammich2017efficient]:
   DRAT proofs tend to contain sequences of RAT lemmas with the same pivot,
   in which case they only compute the list of RAT candidates once per
   sequence and reuse it for all lemmas with the same pivot. We did not
   implement that because the number of RAT introductions in our benchmarks
   is negligible when compared to the number of RUP introductions.

Among state-of-the-art DRAT checkers, `gratgen` is arguably the easiest to
understand (despite implementing a parallel mode), so we advise interested
readers to study that.

\paragraph{\texttt{rupee}} This is the original implementation[^rupee]
of the algorithm to honor unique reason deletions. We use exactly the same
algorithm.  During our research we found one issue in the implementation
which was fixed[^fix-revise-watches].

In previous experiments, `rupee` appeared to be an order of magnitude
slower than `DRAT-trim` [@RebolaCruz2018].  We believe that this overhead
is primarily not a consequence of algorithmic differences but exists mostly
due to implementation details such as parsing[^rupee-parsing].

[^rupee-parsing]: Both `rupee` and `DRAT-trim` use a fixed-size hash table
to locate deleted clauses but `rupee`'s is smaller by one order of magnitude,
which may explain parts of the difference in performance.

Additionally `rupee` does not use core-first unit propagation while the
other checkers do.

4.2 Checker Implementation
--------------------------

Our checker is called `rate`[^rate].  It is a drop-in replacement for a
subset of `drat-trim`'s functionality --- namely the forward and backward
unsatisfiability checks --- with the important difference that it checks
specified DRAT.  When a proof is verified, `rate` can output core lemmas as
DIMACS, LRAT or GRAT.  Otherwise, the rejection of a proof can be supplemented
by a SICK certificate of unsatisfiability.  The representation of the DRAT
proof --- binary or textual -- is automatically detected the same way as
`drat-trim`.  Additionally, compressed input files (Gzip, Zstandard, Bzip2,
XZ, LZ4) are transparently uncompressed.

We provide two options that alter the semantics of the checker:

1. Unit deletions can be skipped with the flag `-d`.
   This makes `rate` check operational DRAT instead of specified DRAT.
   
2. If the flag `--assume-pivot-is-first` is given, the pivot must be the first
   literal in a RAT lemma, otherwise the proof will be rejected.

In terms of performance, `rate` is comparable to other state-of-the-art
checkers as it implements the same optimizations, most importantly backwards
checking with core-first unit propagation.

Among other metrics, `rate` can output the number of reason deletions and
unique reason deletions[^reason-deletions-shrinking-trail]. Other checkers
cannot provide the latter. This might be useful to sanity-check SAT solvers'
proof generation procedures.

We also support a more powerful clausal proof format, DPR (*delete propagation
redundancy*) [@Heule_2017].

The debug build comes with lots of assertions, including checks for arithmetic
overflows and narrowing conversions that cause unintended changes of values.
These checks can also be enabled in the release build with purportedly
minimal impact on performance.

\paragraph{Rust} We chose the modern systems programming language Rust[^rust]
for our implementation.  Among the respondents of the 2019 Stack Overflow
Developer Survey[^so-survey] it is the most loved programming language and
Rust developers have the highest contribution rate to open source projects.

Based on our experience, we believe that, while there may be some
inconveniences with the borrow checker[^partial-ref], it is a viable
alternative to C and C++ for the domain of SAT solving. The first Rust-based
solver to take part in competitions `varisat`[^varisat] is a great example
of this.

4.3. SICK Format
----------------

When a proof is found to be incorrect, our tool outputs an
incorrectness certificate in the previously unpublished SICK
format[^sick-reference-implementation]. This certificate can be used by our
tool `sick-check` to verify incorrectness of the proof without doing any
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
`-1 -2 0`   `0`     `proof_step     = 1 # failed line (1-based) in the proof`
`-1  2 0`            `natural_model  = [-1, ]`
                    `[[witness]]`
                    `failing_clause = [-2, -1, ]`
                    `failing_model  = [2, ]`
                    `pivot          = 1`

\paragraph{Grammar}
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

\paragraph{Explanation}

- `proof_step` specifies the proof step that failed (by offset in the proof,
  starting at one).  For the remainder of this section, let the *lemma*
  denote the clause that is introduced by the referenced proof step.  For a
  textual proof, this corresponds to the line number of the introduction
  instruction that failed.
- `proof_format` describes the proof format to use.
   - `DRAT-arbitrary-pivot`: DRAT checking where the pivot can be any literal
   in the lemma. This requires one witness (counter-example) for each possible
   pivot in the lemma. The pivot has to be specified for each witness.
   - `DRAT-pivot-is-first-literal`: Similar, but there is only one witness.
   The pivot needs to be the first literal in the lemma.  We added the
   distinction between these two formats because it was not clear which one
   should be used universally.
- `natural_model` gives the shared UP-model before checking this proof
  step. This is included to avoid having to do propagation in a checking tool.

Each witness is a counter-example to some redundancy check.

- `failing-clause`: A clause in the formula, which is a resolution candidate
  for the lemma.  This means that the RUP check failed for the resolvent on
  the pivot literal of the lemma and the failing clause.
- `failing-model`: The literals that were added to the natural model (trail)
  when performing the failed redundancy check.
- `pivot`: This specifies the pivot literal.

The absence of a witness means that a RUP check failed.  If the lemma is the
empty clause, a witness is never needed, since the empty clause cannot be RAT.

\paragraph{Semantics} Our tool `sick-check` verifies SICK certificates that
fulfill below properties.

Let $F$ be the accumulated formula up to and excluding the lemma.

1. The proof contains the `proof_step`.
2. The given `natural_model` is the shared UP-model of $F$.
3. For format `DRAT-arbitrary-pivot`, the pivots are identical to the literals in the lemma.
4. For each witness, consisting of `failing_clause`, `failing_model` and `pivot`.
    1. The `failing_clause` is in $F$.
    2. The union of `natural_model` and `failing_model` is the shared UP-model of
       $F \cup \{ \overline{l} \,|\, l \in r\}$
       where $r$ is the resolvent on `pivot` of the lemma and the `failing_clause`.

A SICK certificate can only be produced by checker of specified DRAT, because
to compute the accumulated formula in an operational checker, one would need to
do unit propagation which is avoided by design in the SICK checker.  This is
a potential benefit of a specified checker: the accumulated formula at each
proof step is clearly defined and can be computed without unit propagation.

\paragraph{Contribution} Our contribution is the design of a new syntax that
takes into account the different versions of DRAT with fixed or arbitrary
pivot.


5. Experimental Evaluation
==========================

Here we present a performance evaluation of our checker.  Technical details
are available[^rate-experiments].

We compare the performance of four checkers:

1. `rate`
2. `rate-d` \hfill (the flag `-d` means *"skip unit deletions"*)
3. `drat-trim`
4. `gratgen`

Only `rate` checks specified DRAT, the other three implement operational DRAT.

\paragraph{Benchmark Selection} For a checker, a benchmark shall be a pair of
a SAT problem instance and a solver to produce the proof for this instance.
We take from the 2018 SAT competition[^sc18] both the SAT instances and the
solvers from the main track.  We take several steps to exclude benchmarks that
are not interesting for our purpose:  first we discard all benchmarks where the
instance is satisfiable according to the competition results[^sc18-results].
Secondly we discard the benchmarks (pair of solver and instance) where the
solver timed out for the instance in the competition results because these
combinations will likely time out in our experiments as well.  Running the
checkers on the remaining benchmarks would still have taken several CPU
years. We take a random sample of around one third of the remaining benchmarks
and explicitly select a few interesting ones too. For these benchmarks we
have have run the solver to generate the proof.  Some solvers would time out,
failing to generate a complete proof.  If the solver succeeded, we ran the
four checkers on the proof.

Around two thirds of these proofs are incorrect under specified DRAT.
When `rate` rejects a proof it exits as soon an incorrect instruction is
encountered in the backward pass. This means that it processed only a fraction
of the proof while other checkers would process the entire proof. Hence it
is not useful for benchmarking checker performance to runtimes for proofs
that are rejected under specified DRAT. For the performance comparison we
discard benchmarks with such proofs.

In total we analyze 39 solvers and 120 unsatisfiable instances, making for
over 4000 potential solver-instances pairs as benchmarks. However, after
the sampling and above steps discarding benchmarks that are not relevant
for us, we are left with merely 373 benchmarks where the proof is verified
by all checkers.

\paragraph{Execution} For each benchmark, first the solver is run to
create a proof, then all checkers are run on that proof. For `rate`,
`rate-d` `DRAT-trim`, we ensure that the LRAT proof is verified by the
LRAT checker[^acl2].  For proofs rejected by `rate`, we run `sick-check`,
to double-check that the proof is incorrect under to the semantics of
specified DRAT.

For running the solvers we used the same limits as in the SAT competition ---
5000 seconds CPU time and 24 GB memory using runlim[^runlim]. Similarly for
checking, where  the timeout is 20000 seconds.  We present performance data
as reported by `runlim` --- time in seconds and memory usage in megabytes
(2^20^ bytes).

We performed all experiments on a machine with two AMD Opteron 6272 CPUs with
16 cores each and 220 GB main memory.  We used GNU parallel [@Tange2018]
to run 32 jobs simultaneously. This parallelization slows down the solvers
and checkers, most likely due to increased memory pressure, however, based
on preliminary experiments we believe that the checkers are affected equally
hence it is still a fair comparison.

5.1 Comparison of Checkers
--------------------------

The boxplots for runtime (Figure @fig:box-time) and memory usage (Figure
@fig:box-space) give a high level overview over the checkers' performance.

![Boxplot of checker runtimes across all proofs](p/box-time.pdf){#fig:box-time}

![Boxplot of the checkers' memory usage across all proofs](p/box-space.pdf){#fig:box-space}

On an individual instance two checkers might have different performance
because of different propagation order and, as a result, different clauses
being added to the core.  In Figure @fig:cactus-time and @fig:cactus-space we
show the distribution of performances zoomed in to the most difficult proof
instances.  For easier instances the differences are smaller.  Those plots
suggest that `gratgen` is a bit faster, and `DRAT-trim` is slightly slower
than `rate`. Moreover `rate`, and `rate --skip-unit-deletions` show roughly
the same distribution of runtimes.

![Cactus plot showing the distribution of checker runtimes](p/cactus-time.pdf){#fig:cactus-time}

![Cactus plot showing the distribution of the checkers' memory usage](p/cactus-space.pdf){#fig:cactus-space}

We take a closer look, comparing the performance of two checkers on each
instance, see Figures @fig:cross-rate-d-rate, @fig:cross-rate-d-gratgen and
@fig:cross-rate-d-drat-trim.

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `rate`.
Each marker represents a proof instance.](p/cross-rate-d-rate.pdf){#fig:cross-rate-d-rate}

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `gratgen`.
Each marker represents a proof instance.](p/cross-rate-d-gratgen.pdf){#fig:cross-rate-d-gratgen}

![Cross plot comparing the individual runtimes of `rate --skip-unit-deletions` with `DRAT-trim`.
Each marker represents a proof instance.](p/cross-rate-d-drat-trim.pdf){#fig:cross-rate-d-drat-trim}

In figure @fig:cross-rate-d-rate we see that `rate` exhibits small differences
in specified and operational model.  Figure @fig:cross-rate-d-gratgen shows
that `gratgen` is faster than `rate` on almost all instances.  Similarly,
figure @fig:cross-rate-d-drat-trim shows that `rate` is faster than `DRAT-trim`
on most instances.

![Juxtaposition of the number of reason deletions and the relative
runtime overhead of checking specified DRAT over operational
DRAT.](p/correlation-reason-deletions-time-delta-percent.pdf){#fig:correlation-reason-deletions-time-delta-percent}

![Juxtaposition of the number of reason deletions and the relative overhead
in terms of memory usage of checking specified DRAT over operational
DRAT.](p/correlation-reason-deletions-space-delta-percent.pdf){#fig:correlation-reason-deletions-space-delta-percent}

5.2 Overhead of Reason Deletions
--------------------------------

Figure @fig:correlation-reason-deletions-time-delta-percent suggests
that a large number of reason deletions brings about some runtime
overhead in `rate` when checking specified DRAT as opposed to operational
DRAT. The same seems to hold for the number of unique reason deletions.
A significant overhead in memory consumption occurs in only one
instance, which also has a high number of reason deletions, see figure
@fig:correlation-reason-deletions-space-delta-percent.  This overhead also
occurs for proofs that contain no unique reason deletions.

6. Conclusion
=============

In [Section 3][3. DRAT Proofs without Deletions of Unique Reason Clauses] we
have explained why operational DRAT is required to verify `DRUPMiniSat`-based
solvers' proofs.  We have proposed a patch for these solvers to create proofs
that are correct under either flavor and do not require the workaround of
ignoring unit deletions.

Specified DRAT is necessary to verify solvers' inprocessing steps that
employ deletions of unique reason clauses [@rebola2018two].  We implement an
efficient checker, `rate`, that supports both specified and operational DRAT.
Furthermore specified DRAT comes with the advantage that the accumulated
formula is easy to compute without performing unit propagation.  This enables
us to produce SICK certificates which are small, efficiently check-able
witnesses of a proof's incorrectness.  They report which proof step failed,
which can be used to trace back bugs in solvers and checkers.  We provide
a tool, `sick-check` to check SICK witnesses.

Our initial research question was whether specified DRAT can be checked
as efficiently as operational DRAT.  Based on our benchmarks we provided
evidence that the cost for specified DRAT is, on average, the same but an
excessive number of reason deletions can make it significantly more costly.

7. Future Work
==============

If a checker for specified DRAT were to be adopted, it might be beneficial to
implement a way to perform deletions of non-unique reasons more efficiently
than `rate` does. These deletions do not alter the shared UP-model, but `rate`
does not know this. An optimization could consist of a simple criterion to
determine if whether some reason clause is unique.  A simple criterion is as
follows: if a reason clause for some literal $l$ is deleted, check if unit
clause $l$ is in the formula. If it is, then the deleted reason is not unique
and the shared UP-model will definitely not change.  This criterion might be
sufficient for the proofs produced by the second variant of the patches from
[section 3][3. DRAT Proofs without Deletions of Unique Reason Clauses].

State-of-the-art DRAT checkers are heavily optimized for speed but they keep
the entire input proof and the resulting LRAT proof in memory. If the available
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
[^fix-revise-watches]:
<https://github.com/arpj-rebola/rupee/compare/b00351cbd3173d329ea183e08c3283c6d86d18a1..b00351cbd3173d329ea183e08c3283c6d86d18a1~~~>
[^toml]: <https://github.com/toml-lang/toml>
[^patch-MapleLCMDistChronoBT]:
<https://github.com/krobelus/MapleLCMDistChronoBT/commit/add-unit-before-deleting-locked-clause/>
[^patch-MapleLCMDistChronoBT-keep-locked-clauses]:
<https://github.com/krobelus/MapleLCMDistChronoBT/commit/keep-locked-clauses/>
[^patch-MiniSat]:
<https://github.com/krobelus/minisat/commit/add-unit-before-deleting-locked-clause/>
[^patch-MiniSat-keep-locked-clauses]:
<https://github.com/krobelus/minisat/commit/keep-locked-clauses/>
[^suggestion-add-units]:
<https://github.com/msoos/cryptominisat/issues/554#issuecomment-496292652>
[^mergesat-pr]: <https://github.com/conp-solutions/mergesat/pull/22/>
[^cadical]: <http://fmv.jku.at/cadical/>
[^varisat]: <https://github.com/jix/varisat/>
[^varisat-pr]: <https://github.com/jix/varisat/pull/66/>
[^so-survey]: <https://insights.stackoverflow.com/survey/2019>
[^rust]: <https://www.rust-lang.org/>
[^partial-ref]: <https://jix.one/introducing-partial_ref/>
[^reason-deletions-shrinking-trail]: The metric for the number of unique reason
deletions is called `reason deletions shrinking trail` in the output of `rate`.
[^drupminisat]: The original patch to `MiniSat` to produce DRUP/DRAT proofs on
which others seem to be based.  See <https://www.cs.utexas.edu/~marijn/drup/>
[^gratgen-cf]:
<http://www21.in.tum.de/~lammich/grat/gratgen-doc/Core_First_Unit_Propagation.html>
[^gratgen-noncore-rat-candidates]:
<http://www21.in.tum.de/~lammich/grat/gratgen-doc/Unmarked_RAT_Candidates.html>
[^sick-reference-implementation]: The original implementation is at
<https://github.com/arpj-rebola/rupee>

References
==========
