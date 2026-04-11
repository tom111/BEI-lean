# Guide: Gröbner CM Transfer for Proposition 1.6

## Task

This is the second paper-critical gap for the full formalization of
Proposition 1.6.

The HH side is the first gap: prove that the bipartite / initial-ideal quotient
is genuinely Cohen–Macaulay.

This guide is for the **other** gap:

- once `S / in_<(I)` is known to be Cohen–Macaulay,
- prove that `S / I` is Cohen–Macaulay.

This is the paper-faithful deformation / initial-ideal transfer step.


## Current status

Already proved in the repo:

- the closed-graph Gröbner-basis theorem;
- the identification of the relevant initial ideal;
- the y-shift to the Herzog–Hibi bipartite edge ideal;
- the direct equidimensional surrogate route;
- substantial HH-side infrastructure toward the genuine CM theorem, including:
  - `bipartiteEdgeMonomialIdeal_isWeaklyRegular`;
  - `ringKrullDim_bipartiteEdgeMonomialIdeal`.

Not yet proved:

- a theorem transferring Cohen–Macaulayness from the initial-ideal quotient
  back to the original quotient.

There is currently **no dedicated code theorem** in the repo closing this
deformation step.


## Why this matters

Even if the HH side becomes fully Cohen–Macaulay, Proposition 1.6 is still not
formally complete in the paper's sense until the project can move from

```text
S / in_<(J_G)
```

to

```text
S / J_G.
```

So this is not optional infrastructure. It is one of the two remaining
paper-critical endpoints.


## Recommended timing

This packet is **not** the immediate next target while the HH-side CM theorem is
still open.

Use this guide when either:

- the HH-side CM theorem has been proved; or
- the HH side is sharply blocked and it becomes strategically useful to inspect
  the transfer side in parallel.


## Recommended strategy

### Step 1: isolate the smallest truthful theorem

Do not begin by formalizing the most general textbook statement.

Prefer the narrowest theorem that honestly closes Proposition 1.6, for example:

- a theorem specialized to polynomial rings over fields;
- a theorem specialized to the monomial order already used in this repo;
- or a theorem reducing the transfer to a standard graded / flat degeneration
  result already available in Mathlib or in a manageable local backport.

### Step 2: keep the paper statement visible

The mathematical target is a CM transfer result of the form

```text
S / in_<(I) CM  ->  S / I CM.
```

If the theorem you can prove is weaker or differently packaged, record that
explicitly and say what extra step is still needed to recover Proposition 1.6.

### Step 3: prefer a BEI-usable route over broad abstraction

If there are two options:

- a very general commutative-algebra theorem that would take a long time to
  set up; and
- a narrower graded/deformation theorem sufficient for `J_G`,

prefer the narrower theorem first.


## False routes to avoid

- Do not present an equidimensionality transfer theorem as if it were a
  Cohen–Macaulay transfer theorem.
- Do not assume this is already in Mathlib without checking.
- Do not start from the most general SAGBI / flat-family story unless the
  smaller BEI-relevant route genuinely fails.
- Do not let this packet replace the HH-side CM work in priority unless the HH
  branch is genuinely blocked.


## Definition of done

Best outcome:

- a theorem in the repo that truthfully transfers Cohen–Macaulayness from the
  initial-ideal quotient to the original quotient in the form needed for
  Proposition 1.6.

Minimum acceptable outcome:

- an exact, self-contained statement of the smallest missing deformation /
  Gröbner-transfer theorem needed for the paper route, together with a precise
  explanation of why the current repo still falls short without it.
