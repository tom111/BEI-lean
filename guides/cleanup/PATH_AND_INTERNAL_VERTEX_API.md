# Guide: Extract a Path and Internal-Vertex API

## Goal

Reduce the amount of repetitive list plumbing around paths, internal vertices, head/last
arguments, and nodup support.


## Why this matters

A large fraction of the visual complexity in the Gröbner-basis files is not algebra. It
is path bookkeeping:

- `head?`
- `getLast?`
- `dropLast`
- `tail`
- `Nodup`
- membership in `internalVertices`
- conversion between list support and graph-walk facts

This shows up heavily in:

- [CoveredWalks.lean](/home/tom/BEI-lean/BEI/CoveredWalks.lean)
- [AdmissiblePaths.lean](/home/tom/BEI-lean/BEI/AdmissiblePaths.lean)
- [GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
- [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)
- parts of [GraphProperties.lean](/home/tom/BEI-lean/BEI/GraphProperties.lean)


## Main refactor idea

Build a stable internal API for "admissible path data" instead of repeatedly unpacking
lists by hand.


## Option A: lightweight API only

Keep paths as `List V`, but extract lemmas with consistent names:

- `internal_mem_of_*`
- `internal_ne_head`
- `internal_ne_last`
- `head_mem_path`
- `last_mem_path`
- `internalVertices_reverse`
- `subpath_preserves_internal_*`

This is the safest short-term option.


## Option B: small structure wrapper

Introduce a local structure representing a path with:

- endpoint data;
- `Nodup`;
- chain/walk property.

Then prove helper lemmas once for the structure.

This may help, but only if it does not create too much coercion overhead.
Do not do this unless it clearly simplifies at least two major files.


## Immediate extraction targets

## 1. endpoint exclusion lemmas in `GroebnerBasisSPolynomial.lean`

Current examples:

- `not_head_of_internal'`
- `not_last_of_internal'`

These should live in the shared path API, not inside one theorem file.


## 2. reverse/take/drop internal-vertex lemmas in `CoveredWalks.lean`

There are many good local lemmas there, but the file is too large for them to remain
hidden. Promote the generally useful ones into a coherent section.


## 3. shortest-walk direction lemmas in `GraphProperties.lean`

The lemmas:

- `isDW_first_lt`
- `isDW_head_lt`
- `isDW_penultimate_lt`

are exactly the kind of local graph-walk API that should be grouped and documented.


## Cleanup rule

If a lemma mentions only:

- lists,
- `internalVertices`,
- `Nodup`,
- head/last,
- or walk support plumbing,

and does not mention a theorem-specific construction, it probably belongs in the shared
path API.


## Naming guidance

Prefer names that describe the path fact, not the theorem where it happened to be
needed. Avoid one-off names with apostrophes unless there is a real conflict.


## Anti-patterns to avoid

- leaving generic path lemmas buried 1500 lines deep in one theorem file;
- proving the same endpoint-exclusion fact twice under slightly different names;
- folding path plumbing into major algebraic proofs.


## Definition of done

This guide is complete when the heavy Gröbner and covered-walk proofs can invoke a small,
recognizable path API instead of manipulating `List` structure ad hoc.
