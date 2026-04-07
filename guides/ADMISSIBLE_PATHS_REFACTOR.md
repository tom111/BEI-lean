# Guide: Admissible Paths Refactor Packet

## Original task / context

Review the admissible-path layer against the paper and look for bugs, dead code, or
possible simplification.

Audit result:

- no mathematical bug was found in the admissible-path layer;
- the definitions are paper-faithful in content;
- small direct cleanups were already applied locally:
  - deprecated `List.Chain'` replaced by `List.IsChain` in the admissible-path predicate;
  - unnecessary `DecidableEq V` burden removed from the core membership theorem block.

The main remaining issue is not correctness but proof structure: there is substantial
duplication in the “split below `i` / split above `j`” machinery in
`BEI/AdmissiblePaths.lean`.


## Mathematical status

The key objects already match the paper:

- `IsAdmissiblePath` in `/home/tom/BEI-lean/BEI/GraphProperties.lean`
- `pathMonomial` in `/home/tom/BEI-lean/BEI/AdmissiblePaths.lean`
- `groebnerElement` in `/home/tom/BEI-lean/BEI/AdmissiblePaths.lean`
- `groebnerElement_mem` in `/home/tom/BEI-lean/BEI/AdmissiblePaths.lean`

The only nontrivial translation choice is admissibility condition (iii):

- the paper says no proper subset of the internal vertices, taken in the inherited
  order, gives a path;
- Lean encodes this as “no proper sublist with the same endpoints is still an
  outside-interval walk”.

Given `Nodup`, inherited order, and the fixed endpoints, this is a correct
formalization choice. Do not change it unless you find an actual mathematical mismatch.


## Files

Primary file:

- `/home/tom/BEI-lean/BEI/AdmissiblePaths.lean`

Supporting definition:

- `/home/tom/BEI-lean/BEI/GraphProperties.lean`


## What to improve

The main duplication is between:

- `pathMonomial_split_below`
- `pathMonomial_split_above`
- `subwalk_props`
- `subwalk_props_above`

and the corresponding Case A / Case B branches in:

- `groebnerElem_mem_aux`

The current code is mathematically fine, but the two branches are structurally very
similar and expensive to maintain. The goal is to reduce duplication without changing
the theorem surface or drifting away from the paper.


## Recommended scope

This is a refactor packet, not new mathematics.

Acceptable outcomes:

1. factor duplicated list/splitting infrastructure into shared helper lemmas;
2. reduce duplicated proof scripts in the two branches of `groebnerElem_mem_aux`;
3. improve local comments/docstrings where the split logic is hard to parse.

Not acceptable:

- rewriting the admissible-path predicate for style only;
- changing theorem names or public theorem statements unless there is a compelling
  reason;
- broad reorganization across multiple files;
- replacing the paper-faithful proof shape with a totally different argument just to
  make Lean shorter.


## Concrete refactor targets

### Target 1: shared split-path infrastructure

The lemmas

- `subwalk_props`
- `subwalk_props_above`

have a large common prefix:

- locating `v₀` by `idxOf`;
- proving `k > 0` and `k < length - 1`;
- extracting head/last facts for `β` and `α'`;
- transporting `Nodup` and chain facts to subwalks.

Try to package the common setup into one or more smaller helpers. For example:

- a helper that packages the generic `idxOf` / head / last / length facts for a chosen
  internal vertex `v₀`;
- a helper that describes the two derived subwalks `β := drop k` and
  `α' := (take (k+1)).reverse`;
- a helper for the internal-vertex list decomposition
  `internalVertices π = ... ++ [v₀] ++ ...`.

Do not force everything into one giant structure if that makes proof search worse.
Two or three smaller helpers is better.

### Target 2: shared path-monomial factorization scaffolding

The lemmas

- `pathMonomial_split_below`
- `pathMonomial_split_above`

also duplicate a lot of list decomposition and filter-manipulation work.

If possible, isolate shared sublemmas about:

- membership of subwalk internals in the original internal-vertex list;
- non-membership of endpoints in the internal-vertex lists;
- filter transport along the split decomposition.

It is fine if the final two factorization lemmas remain separate; the real win is to
remove repeated low-level list boilerplate.

### Target 3: lighten the two induction branches

The two main branches in `groebnerElem_mem_aux` should ideally read as:

1. choose the extremal internal vertex;
2. obtain subwalk properties from the shared helper(s);
3. apply induction hypothesis to the two smaller paths;
4. apply the relevant path-monomial factorization lemma;
5. close with the algebraic identity.

Right now too much branch-local list setup is still inlined.


## False routes / cautions

- Do not change the mathematical content of condition (iii) unless you find a real bug.
- Do not merge the “below” and “above” cases into one theorem if the resulting proof is
  significantly harder to read.
- Do not add a large custom path datatype. The current `List V` representation is
  already wired into the rest of the file.
- Do not spend time on unrelated linter cleanup elsewhere in `GraphProperties.lean`.
- Do not touch the public Gröbner-basis theorems in `BEI/GroebnerBasis*.lean` unless
  this refactor forces a tiny import/name adjustment.


## Definition of done

Best outcome:

- substantial reduction of duplicated proof infrastructure in
  `BEI/AdmissiblePaths.lean`;
- the main induction proof becomes easier to read;
- theorem statements and mathematical content remain unchanged.

Minimum acceptable outcome:

- factor one real shared helper block out of the paired “below/above” lemmas;
- remove a visible chunk of duplication without destabilizing the file.


## Verification

Build at least:

- `lake build BEI.AdmissiblePaths`

Only update status docs if theorem names or file structure change in a meaningful way.
This is mainly a proof-engineering cleanup packet.
