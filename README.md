# Binomial Edge Ideals

A Lean 4 / Mathlib formalization of the paper "Binomial edge ideals and
conditional independence statements" by Jürgen Herzog, Takayuki Hibi,
Freyja Hreinsdottir, Thomas Kahle and Johannes Rauh.

- Advances in Applied Math: https://doi.org/10.1016/j.aam.2010.01.003
- Arxiv: https://arxiv.org/abs/0909.4717

All paper results are formalized in Lean. `lake build` succeeds with no
`sorry` on the paper path.

Documentation and blueprint:

- [Formalization map](FORMALIZATION_MAP.md)
- [Blueprint source](docs/index.md)
- [Published blueprint](https://tom111.github.io/BEI-lean/)

Material outside the main formalization lives in [`Supplement/`](Supplement/),
which is not built by the default target.
