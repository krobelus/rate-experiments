% Complete DRAT Proof Checking
% Johannes Altmanninger
% November 13, 2019

## Roadmap

- Introduction
- Problem statement
- Remedies
    - Solvers
    - Checkers
- Conclusion

## DRAT Proofs

> - Used for verifying the SAT solvers' unsatisfiability results
> - Log of clause introductions and deletions
> - Proof checker can reproduce unsatisfiability
> - Introduced clauses are redundant (RAT)

## Preliminaries

> - Central reasoning technique: *unit propagation* exhaustively literals in unit clauses
> - *Unit clause*: one non-falsified literal
>     - $\supseteq$ *Reason clause*: reason for satisfying some literal
>         - $\supseteq$ *Unique reason clause*: only possible reason

> - Deletion unique reason clauses shrinks the assignment!

## Two flavors of DRAT

- *Operational DRAT* ignores deletions of unit clauses
    <ul>
    <li>Much easier to implement *efficiently*</li>
    <li>Implemented by state-of-the-art checkers</li>
    </ul>
    
- *Specified DRAT* honors all deletions.

<!--
    <ul>
    <li>Required for verifying proofs with arbitrary deletions</li>
    <li>Invaluable for efficently computing properties about proofs</li>
    </ul>
-->

## Motivation for using specified DRAT

> - Proofs for advanced inprocessing techniques may emit arbitrary deletions
> - Computing properties of a proof is much less costly
> - Conceptually simpler
 
> - Disadvantage: checker implementation is more difficult
    (but solvers could still produce produce proofs that are correct in
    either flavor).

## Research Question

> Is it possible to check specified DRAT as efficiently as operational DRAT?

## Current status

- Many DRAT proofs incorrect under specified DRAT
- Legit proofs might be incorrect under operational DRAT
  (when relevant deletions are ignored)

## Incorrectness Scenarios

> - Specified DRAT:
    <ul>
        <li>Some unique reason clause is *deleted*</li>
        <li>Proof fails due to **absence** of clause</li>
    </ul>
> - Operational DRAT:
    <ul>
        <li>Deletion of unique reason clause is *not deleted*</li>
        <li>Proof fails due to **presence** of clause (c.f. non-monotonicity of RAT)</li>
    </ul>

## Making Proofs Conform to Specified DRAT

> - Prerequisite for adoption of specified DRAT
> - Most solvers do not use inprocessing techniques whose verification
  requires specified DRAT...
> - ... so they should not produce any unique reason deletions.

## Why are so many proofs incorrect under specfied DRAT?

> - DRUPMinisat-based solvers delete unique reason clauses that are still
    used to show unsatisfiability...
> - ... but an operational checker ignores those deletions, so
    verification succeeds.
> - Why generate the deletions in the first place?<br/>
    We provide patches to avoid them!

## Checking Specified DRAT

- Need to implement deletions that actually discard information.
- Non-trivial when combined with other optimizations like backwards checking
- Efficient algorithm exists, but implementations were not competitive.

##
<h2>Our checker:
    <span style="text-transform: none;">rate</span>
</h2>

> aka "rate ain't trustworthy either"

> - MIT licensed, openly developed DRAT proof checker
  <https://github.com/krobelus/rate>
> - Supports specified and operational DRAT
> - Competitive performance
> - "seems like a nice piece of work, much-much nicer to read than drat-trim"

## rate vs. other checkers

![](https://raw.githubusercontent.com/krobelus/rate-experiments/master/slides/cactus.png)

## Answering the Research Question

> Is it possible to check specified DRAT as efficiently as operational DRAT?

- On the average instance, the cost is the same.
- Specified DRAT is usually more costly on proofs with many deletions.

## Overhead of reason deletions

![](https://raw.githubusercontent.com/krobelus/rate-experiments/master/slides/overhead.png)

## Double Checking Incorrectness Results

> - Many proofs rejected by rate (*could that be a bug?*)
- SICK format is a small, efficiently checkable counter-example
  for a clausal proof
- Comprises the incorrect proof step & the partial assignment
- Checked with a simple independent tool (called `sick-check`)
- `sick-check` would be much more complex and less efficient 
  with operational DRAT (essentially defeating its purpose)

## Conclusion

> - Specified DRAT is required for
    <ul>
        <li>verifying advanced inprocessing techniques</li>
        <li>reasoning about a proof efficiently</li>
    </ul>

> - We pave the way for specified DRAT by
    <ul>
        <li>patching solvers to conform to it</li>
        <li>providing an efficient checker</li>
        <li>specifying SICK witnesses of proof incorrectness</li>
    </ul>

## Outlook

- DPR as more powerful proof format DRAT
    - we already implement it
    - lack of large benchmarks
- LRAT as alternative to DRAT?
    - saves time & costs space
    - only one solver supports it
