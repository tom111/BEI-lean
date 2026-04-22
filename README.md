# Binomial Edge Ideals

This is an attempt to formalize the paper "Binomial edge ideals and conditional independence statements" by Jürgen Herzog, Takayuki Hibi, Freyja Hreinsdottir, Thomas Kahle and Johannes Rauh.

- Advances in Applied Math: https://doi.org/10.1016/j.aam.2010.01.003
- Arxiv: https://arxiv.org/abs/0909.4717

The current development covers the main Gröbner-basis and prime-decomposition backbone
of the paper, including Theorems 1.1, 2.1, 3.2, the Section 3 dimension formula, and
the minimal-prime description. It also includes the binary-output Section 4
single-statement bridge, specification bridge, and transferred radicality / prime
decomposition / minimal-prime results for CI ideals. The paper-faithful
Cohen–Macaulay statement of Proposition 1.6 is now fully formalized and axiom-clean,
along with the direct equidimensional surrogate route and the path-graph example. The
remaining paper-level gaps are the full Cohen–Macaulay branches of Corollaries 3.4
and 3.7; the current Lean development still represents those by equidimensional
surrogates.

A full `lake build` currently succeeds. The only remaining `sorry`s live in the
dormant infrastructure file `toMathlib/HeightAdditivity.lean` and the archived
supplementary file `Supplement/RauhApproach.lean`, not on the active paper path.

Documentation and blueprint scaffold:

- [Formalization map](FORMALIZATION_MAP.md)
- [Blueprint source](docs/index.md)
- [Published blueprint](https://tom111.github.io/BEI-lean/)

Supplementary archived code that is outside the main paper formalization lives in
[`Supplement/`](Supplement/), currently including an alternative Rauh-style proof attempt
for Theorem 2.1.
