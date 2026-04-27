# Guide: Decompose `BEI/Equidim.lean` by Mathematical Role

**Superseded by [`work_packages/EQUIDIM_FILE_SPLIT.md`](../work_packages/EQUIDIM_FILE_SPLIT.md)**
(2026-04-23).

This high-level note is kept only as a historical pointer. The active plan
is the work package, which carries:

- concrete file-by-file targets with line ranges and declaration assignments;
- the in-place refactor required for the 2480-line iterated-regularity block
  before any move;
- migration order and `private` → public discipline;
- preserved-statement and verification rules;
- a cross-reference to the toMathlib extraction commit `d53e84d`.
