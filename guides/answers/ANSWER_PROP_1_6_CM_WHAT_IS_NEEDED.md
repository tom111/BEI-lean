# Guide: What Is Actually Needed for the Real CM Proposition 1.6?

## Preserved question

Claude asked:

> What is exactly needed for the real CM Prop 1.6?
>
> The direct equidimensional route is already proved, but the paper's proof uses
> the initial-ideal route. Which pieces of real Cohen–Macaulay theory are
> actually on the critical path for the paper-faithful proof?


## Short answer

The new general CM foundation files

- `toMathlib/CohenMacaulay/Defs.lean`
- `toMathlib/CohenMacaulay/Basic.lean`

are good and worth keeping, but they are **not** the critical path for the
paper-faithful proof of Proposition 1.6.

For Proposition 1.6 itself, the two real gaps are:

1. a Herzog–Hibi bipartite Cohen–Macaulay theorem for the graph `Γ`;
2. a Gröbner deformation transfer theorem
   `S / in_<(I) CM -> S / I CM`.

Everything else in the BEI-specific reduction is already proved.


## Current proved reduction

The following Proposition 1.6 reduction steps are already formalized:

1. closed graph hypotheses and Proposition 1.6 combinatorics;
2. quadratic Gröbner basis for `J_G`;
3. identification of `in_<(J_G)` as the relevant monomial ideal;
4. the y-shift to the bipartite edge ideal;
5. proof that the bipartite graph satisfies the Herzog–Hibi conditions.

So the paper route has already been reduced to two algebra theorems:

### Gap A: HH bipartite CM theorem

For the Herzog–Hibi bipartite graph `Γ`, prove that the quotient by its edge
ideal is Cohen–Macaulay.

### Gap B: Gröbner transfer theorem

For the relevant polynomial quotient, prove that Cohen–Macaulayness transfers
from the initial ideal quotient back to the original ideal quotient.


## What this means for the current CM backport track

The forward depth inequality packet in

- `guides/work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md`

is still a legitimate **general CM foundation** task.

But it is **not** the next paper-critical task for Proposition 1.6.

That packet should therefore be treated as:

- useful infrastructure for the real CM branch;
- not the immediate critical path for the paper route.


## Recommended task split

Keep two explicit subtracks inside the real CM branch:

### Track A: paper-critical Prop 1.6 route

Immediate next work should target one of:

1. the HH bipartite CM theorem;
2. the Gröbner transfer theorem.

This is the track that could honestly finish the paper-style Proposition 1.6.

### Track B: general CM foundation backport

Continue the PR/backport work in `toMathlib/CohenMacaulay/` when it is
genuinely useful, but do not confuse it with the immediate Proposition 1.6
critical path.

The forward depth inequality belongs here.


## Recommendation on what to do next

Do **not** send Claude straight back to the forward depth inequality as if it
were the Prop 1.6 blocker.

Instead, the next theorem packet for the paper route should be a decision packet
for Gap A versus Gap B:

- either isolate the smallest truthful Herzog–Hibi CM theorem for the current
  bipartite graph setup;
- or isolate the smallest truthful Gröbner transfer theorem needed for the
  existing initial-ideal reduction.

My recommendation is to start with **Gap A** first:

- the HH theorem is more BEI-specific and closer to the paper;
- it may admit a more targeted route than broad general CM infrastructure;
- it keeps the project aligned with the paper instead of drifting into general
  regular-sequence theory.


## False routes to avoid

- Do not describe `Basic.lean` as if it were already closing Proposition 1.6.
- Do not remove the new CM foundation files; they are still useful.
- Do not collapse the distinction between:
  - general CM backport work, and
  - the two paper-critical CM gaps.
- Do not claim that proving the forward depth inequality will by itself finish
  the paper route for Proposition 1.6.


## Definition of done for this guide

This guide is an answer/decision note, not a theorem packet.

After adopting it, the guide queue should make clear:

1. Proposition 1.6 paper route:
   HH bipartite CM theorem and Gröbner transfer are the two real blockers.
2. General CM backport:
   `Defs.lean`, `Basic.lean`, and the forward depth inequality are supporting
   infrastructure, not the immediate Prop 1.6 endpoint.
