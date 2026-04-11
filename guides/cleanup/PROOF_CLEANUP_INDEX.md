# Proof Cleanup Guides

These guides are for refactoring the existing formalization so that proofs become:

- shorter;
- more human-readable;
- easier for Claude to extend without regressions.

Recommended order:

1. [PUBLIC_THEOREM_LAYER.md](/home/tom/BEI-lean/guides/cleanup/PUBLIC_THEOREM_LAYER.md)
2. [EVALUATION_MAP_API.md](/home/tom/BEI-lean/guides/cleanup/EVALUATION_MAP_API.md)
3. [PATH_AND_INTERNAL_VERTEX_API.md](/home/tom/BEI-lean/guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
4. [MONOMIAL_AND_FINSUPP_API.md](/home/tom/BEI-lean/guides/cleanup/MONOMIAL_AND_FINSUPP_API.md)
5. [FILE_SPLITTING_PLAN.md](/home/tom/BEI-lean/guides/cleanup/FILE_SPLITTING_PLAN.md)
6. [LINTER_AND_STYLE_CLEANUP.md](/home/tom/BEI-lean/guides/cleanup/LINTER_AND_STYLE_CLEANUP.md)

General rule:

- do not try to shorten proofs by golfing tactics;
- first extract the right helper lemmas and abstractions;
- only then simplify the top-level proof scripts.

The target is not "fewer lines at any cost". The target is:

- the public theorem layer reads like the paper;
- the private helper layer absorbs the low-level Lean plumbing;
- recurring proof patterns appear once, not five times.
