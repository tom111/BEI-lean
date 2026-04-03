# CM PR Import / Backport Guides

This directory contains guides for selectively importing and backporting code from the
mathlib Cohen–Macaulay pull request referenced in
[TODO.md](/home/tom/BEI-lean/TODO.md) as PR `#26218`.

Current guide:

- [MINIMAL_IMPORT_AND_BACKPORT.md](/home/tom/BEI-lean/guides/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md)

Purpose:

- keep the BEI project pinned to mathlib `v4.28.0` as long as possible;
- import only the smallest CM slice actually needed;
- avoid turning the whole repo into an experimental fork of mathlib master;
- preserve a clean paper-faithful formalization path.
