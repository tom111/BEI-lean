# Binomial Edge Ideals

This is an attempt to formalize the paper "Binomial edge ideals and conditional independence statements" by Jürgen Herzog, Takayuki Hibi, Freyja Hreinsdottir, Thomas Kahle and Johannes Rauh.

- Advances in Applied Math: https://doi.org/10.1016/j.aam.2010.01.003
- Arxiv: https://arxiv.org/abs/0909.4717

The current development covers the main Gröbner-basis and prime-decomposition backbone
of the paper, including Theorems 1.1, 2.1, 3.2, the Section 3 dimension formula, and
the minimal-prime description. It also includes the binary-output Section 4
single-statement bridge, specification bridge, and transferred radicality / prime
decomposition / minimal-prime results for CI ideals. The main remaining paper gap is
the Cohen–Macaulay branch of Proposition 1.6. The Section 3 CM corollaries and the
Section 4 CI-ideal transfers are now formalized. A direct equidimensional surrogate
variant of Proposition 1.6 is also proved, but the full depth-based Cohen–Macaulay
statement from the paper is still open.

Documentation and blueprint scaffold:

- [Formalization map](FORMALIZATION_MAP.md)
- [Blueprint source](docs/index.md)
- [Published blueprint](https://tom111.github.io/BEI-lean/)
