# Answer: HH quotient CM at a non-augmentation prime

Deep-model reply (2026-04-18) to the question preserved from
`questions/HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md`. This is the authoritative
mathematical answer that the active work package
`guides/work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md` now follows.

## Preserved question

Let `K` be a field, `n ≥ 2`, `σ := {x_0,…,x_{n-1}, y_0,…,y_{n-1}}`, `S := K[σ]`,
and `G` a simple graph on `[n]` satisfying the Herzog–Hibi conditions

  (i)  diagonal   : `{i, i+1} ∈ E(G)` for all `i < n-1`;
  (ii) transitivity: `{i, j+1}, {j, k+1} ∈ E(G)` with `i < j < k` ⟹ `{i, k+1} ∈ E(G)`.

Let `I = (x_i · y_j : i ≤ j, j+1 < n, {i, j+1} ∈ E(G))` and `R := S/I`.
Already formalised: `dim R = n+1`, `R` equidimensional, `I` radical, a
regular sequence `fullRegSeq` of length `n+1` in `R` (weakly regular on
every R_p), `R_{m⁺}` CM at the augmentation, polynomial-rings-over-CM
globally CM (PR #28599 backport), CM-localises.

Open: show `R_p` is CM for every prime `p ⊄ m⁺`. A counterexample
`n=4, G=K_4, p = (x_0, x_1, y_0, y_1, y_2, x_3 − 1)` rules out the naive
"R_p is a polynomial-ring localisation" shortcut.

## Q1 / Q7 — strategy choice

**Do not induct on n.** The cleanest route, given the PR #28599 backport, is
to keep the existing F2 decomposition strategy but change the tensor-CM
endpoint:

  R_p ≅ (A^red_{G', m_{G'}} ⊗_K K[Λ ⊔ U][s_U⁻¹])_𝔓

where `A^red_{G'}` is a **reduced** HH ring and `m_{G'}` is its augmentation
ideal. Since `A^red_{G', m_{G'}}` is already CM (formalised), polynomial-
over-CM + localisation proves CM of the right-hand side. This avoids
induction on n, flat-local CM, Reisner / shellability / Alexander duality,
and explicit height computations. The only genuinely structural work is the
monomial-localisation decomposition; the only extra algebra lemma is a
small tensor-polynomial-localisation lemma — not a flat-local CM criterion.

Induction on n is possible but messier: the natural factor after
localisation is a **reduced** HH ring, not a full HH ring, because the
trailing isolated pair of the full HH ring is often absent or killed.
Running induction on full HH rings would force either a simultaneous
induction for reduced HH rings or an additional global-CM descent from
`A[t_1, t_2]` to `A`. The direct F2 endpoint avoids this.

## Q2 / Q7 (a)–(d) — structural decomposition (corrected)

The naive claim `R_p ≅ (R_{G'})_q ⊗_K L` with the **full** HH quotient is
not right in general. The canonical factor is the **reduced** HH quotient
of a smaller HH graph. The full HH ring on `r+1` vertices would be
`R_{G'} ≅ A^red_{G'}[x'_r, y'_r]`, but the trailing isolated pair `x'_r,
y'_r` is not naturally present in the localised original ring.

### Step 1 — unit, killed, surviving variables

Let `Γ_G` be the bipartite graph with vertices `σ` and edges

  `x_i ─ y_j  ⟺  i ≤ j, j+1 < n, {i, j+1} ∈ E(G)`.

Given a prime `p ⊄ m⁺` of `R`, set

  U := { v ∈ σ : v̄ ∉ p }        (units in R_p)

Because `p` is prime and `x̄_i · ȳ_j = 0` on every edge, `U` is
**independent** in `Γ_G`.

  N(U) := { z ∈ σ \ U : ∃ u ∈ U, {z, u} ∈ E(Γ_G) }

For each `z ∈ N(U)` we have `zu = 0` in R and `u` unit in R_p, hence
`z̄ = 0` in R_p.

  W := σ \ (U ∪ N(U))           (surviving nonunit vars; W ⊆ p)

Let `s_U := ∏_{u ∈ U} u`. There is a canonical isomorphism

    Φ_U : R[s_U⁻¹]  ≅  (K[W] / I(Γ_G|_W))  ⊗_K  K[U][s_U⁻¹]

given on generators by

    Φ_U(v̄) = v̄ ⊗ 1          (v ∈ W)
    Φ_U(v̄) = 0              (v ∈ N(U))
    Φ_U(v̄) = 1 ⊗ v          (v ∈ U).

Well-definedness: check every original edge `a b`. If both endpoints lie
in `W`, then `ab ∈ I(Γ_G|_W)`. If one endpoint is in `U`, the other is in
`N(U)` and maps to 0. Endpoints cannot both lie in `U` because `U` is
independent.

Since `s_U ∉ p`, localisation–localisation gives

    R_p  ≅  ((K[W] / I(Γ_G|_W))  ⊗_K  K[U][s_U⁻¹])_𝔓

where `𝔓 = Φ_U(p)`.

### Step 2 — paired survivors vs isolated survivors

Set

  C := { i < n−1 : x_i ∈ W and y_i ∈ W }
  Λ := W \ { x_i, y_i : i ∈ C }.

So `Λ` is one-sided survivors plus possibly `x_{n-1}, y_{n-1}`, which are
always isolated.

**Key HH-combinatorial fact.** Every variable in `Λ` is isolated in
`Γ_G|_W`.

Proof for `x_i ∈ W, y_i ∉ W`. Since `x_i ∈ W`, `y_i ∉ U` (because
`x_i ─ y_i` is an edge for `i < n−1`). Hence `y_i ∈ N(U)`: there is
`x_a ∈ U` with `x_a ─ y_i`, giving `a ≤ i, {a, i+1} ∈ E(G)`. Suppose
`x_i` has an edge to some `y_j ∈ W`. Then `i ≤ j, {i, j+1} ∈ E(G)`.
Case `j = i` is impossible (since `y_i ∉ W`). So `i < j`. Also `a < i`
(else `x_i ∈ U`). HH transitivity applied to `{a, i+1}, {i, j+1}` gives
`{a, j+1} ∈ E(G)`, so `x_a ─ y_j` is an edge, and `x_a ∈ U` forces
`y_j ∈ N(U)`, contradicting `y_j ∈ W`. Therefore `x_i` is isolated in
`Γ_G|_W`. The `y_i ∈ W, x_i ∉ W` case is dual. Hence

    Γ_G|_W = Γ_C ⊔ { isolated vertices Λ }.

(This is the already-formalised L3.)

### Step 3 — the smaller HH graph G'

Write `C = { c_0 < c_1 < … < c_{r-1} }` and define `G'` on `{0, …, r}` by

  `{a, b+1} ∈ E(G')  ⟺  {c_a, c_b + 1} ∈ E(G)`   (for `0 ≤ a ≤ b < r`).

Then **G' satisfies the HH conditions**.

- Diagonal: `{c_a, c_a+1} ∈ E(G)` by HH diagonal for G, so
  `{a, a+1} ∈ E(G')`.
- Transitivity: if `{a, b+1}, {b, c+1} ∈ E(G')` with `a < b < c`, then
  `{c_a, c_b+1}, {c_b, c_c+1} ∈ E(G)`, and `c_a < c_b < c_c`, so HH
  transitivity for G gives `{c_a, c_c+1} ∈ E(G)`, i.e.
  `{a, c+1} ∈ E(G')`.

Define the reduced HH ring

  A^red_{G'} := K[x'_0, …, x'_{r-1}, y'_0, …, y'_{r-1}]
              / (x'_a y'_b : 0 ≤ a ≤ b < r, {a, b+1} ∈ E(G')).

There is a canonical isomorphism

  Ψ_C : K[W] / I(Γ_G|_W)  ≅  A^red_{G'}  ⊗_K  K[Λ]

given on generators by

  Ψ_C(x̄_{c_a}) = x̄'_a ⊗ 1,   Ψ_C(ȳ_{c_a}) = ȳ'_a ⊗ 1,   Ψ_C(λ̄) = 1 ⊗ λ  (λ ∈ Λ).

Well-defined because edges among paired variables correspond exactly to
the defining edges of `G'`, and variables in `Λ` are isolated.

Combining `Φ_U` and `Ψ_C`:

  R_p  ≅  (A^red_{G'}  ⊗_K  K[Λ ⊔ U][s_U⁻¹])_{𝔓'}.

The prime `𝔓'` contracts to the augmentation ideal of `A^red_{G'}`:
every variable of `A^red_{G'}` comes from a variable in `W ⊆ p`, so the
contraction contains all `x'_a, y'_a`, hence equals the augmentation
maximal ideal `m^red_{G'}`. Therefore

  R_p  ≅  (A^red_{G', m^red_{G'}}  ⊗_K  K[Λ ⊔ U][s_U⁻¹])_{𝔓''}.

This is the form to target in Lean.

### Counterexample check: n=4, G=K_4

HH edges: `x_0y_0, x_0y_1, x_1y_1, x_0y_2, x_1y_2, x_2y_2`.
Take `p = (x_0, x_1, y_0, y_1, y_2, x_3 − 1)`.

  U = {x_2, x_3, y_3},  N(U) = {y_2},  W = {x_0, x_1, y_0, y_1},
  C = {0, 1},          Λ = ∅,        G' = K_3 on {0, 1, 2}.

Reduced HH ring:

  A^red_{K_3} = K[x'_0, x'_1, y'_0, y'_1] / (x'_0 y'_0, x'_0 y'_1, x'_1 y'_1).

Decomposition:

  R_p ≅ (A^red_{K_3, m} ⊗_K K[x_2, x_3, y_3][(x_2 x_3 y_3)⁻¹])_𝔓
      ≅ (A^red_{K_3, m} ⊗_K K[x_2, x_3, y_3]_{(x_3 − 1)})_𝔓

where `𝔓 = (x'_0, x'_1, y'_0, y'_1, x_3 − 1)`. This matches the
prior prose expectation, with the critical correction that the HH factor
is the **reduced** n=3 triangle HH ring, not the full one with trailing
isolated pair.

## Q6 — the tensor-localisation-CM lemma

> **Lemma** (polynomial-localised tensor over a field preserves CM).
> Let `K` be a field, `A` a Noetherian `K`-algebra with `IsCohenMacaulayRing A`,
> `τ` a finite type, `s ∈ K[τ]`, and `B := K[τ][s⁻¹]`. Then for every prime
> `𝔓 ⊂ A ⊗_K B`, the localisation `(A ⊗_K B)_𝔓` is Cohen–Macaulay.

**Proof sketch.**

1. Canonical equivalence `A ⊗_K K[τ] ≅ A[τ]` (MvPolynomial base change).
2. Under this, `A ⊗_K K[τ][s⁻¹] ≅ A[τ][s_A⁻¹]`, where `s_A` is the image
   of `s` under `K[τ] → A[τ]`.
3. `A` is CM ⟹ `A[τ]` is CM, by the backported
   `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`.
4. CM localises ⟹ `A[τ][s_A⁻¹]` is CM.
5. Localising again at `𝔓` gives CM.

**Lean status.**

- Polynomial CM: `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`
  (available — `toMathlib/CohenMacaulay/Polynomial.lean`).
- CM localises: already in the development.
- CM transfer through `RingEquiv`: already available.
- The ring iso `A ⊗_K K[τ][s⁻¹] ≅ A[τ][s_A⁻¹]` is the only small algebraic
  bridge still to formalise. Straightforward generalisation of the existing
  `polynomialAwayTensorEquiv` in `toMathlib/PolynomialAwayTensor.lean`.

For the BEI application, take `A = A^red_{G', m^red_{G'}}` and
`B = K[Λ ⊔ U][s_U⁻¹]`. The existing
`isCohenMacaulayLocalRing_reducedHH_at_augIdeal` gives `A` CM local; promote
to `IsCohenMacaulayRing A` via CM-localises; the lemma above applies. This
is exactly the missing L7 replacement.

## Q3 — subsequence of `fullRegSeq` (ruled out)

The "delete units from fullRegSeq" shortcut does **not** work. In the
counterexample,

    fullRegSeq = [x_0 + y_0, x_1 + y_1, x_2 + y_2, x_3, y_3].

Inside `R_p`: `x_2 + y_2 = x_2` is a unit (since `x_2 ∉ p`, `y_2 = 0`);
`x_3, y_3` are units. The subsequence lying in `p · R_p` has length 2.
But `dim R_p = 3`: using the decomposition, `dim A^red_{K_3, m} = 2` and
`dim K[x_2, x_3, y_3]_{(x_3 − 1)} = 1`. So the surviving subsequence is
short, and this route cannot prove CM globally.

## Q4 — direct parameters (sanity check only)

For the counterexample, an explicit system of parameters is
`x_0 + y_0, x_1 + y_1, x_3 − 1`. Regularity follows from the tensor
decomposition: the first two are weakly regular on `A^red_{K_3, m}`, and
after quotienting, `x_3 − 1` is regular on the polynomial-local factor;
tensoring over K preserves injectivity. For a general `p ⊄ m⁺`, the
decomposition gives a conceptual recipe (reduced HH augmentation sequence
+ parameters of the polynomial-local factor). Not formalisation-friendly
as a primary route; the polynomial-CM theorem avoids the height
infrastructure.

## Q5 — Gröbner / edge-ideal route (ruled out)

A direct CM criterion for bipartite HH edge ideals would require
shellability / Reisner / Alexander duality or a Gröbner-degeneration
CM-transfer theorem. All heavier than the F2 endpoint. Moreover,
unmixedness + `fullRegSeq`-at-augmentation is not enough globally
(see Q3). Not recommended.

## Sanity: does this reprove Stanley–Reisner CM theory?

**No.** The proof uses only:

1. monomial localisation of an edge ideal;
2. HH transitivity to identify the surviving non-isolated subgraph as a
   reduced HH graph;
3. the already-formalised reduced-HH-at-augmentation CM theorem;
4. polynomial-over-CM;
5. localisation of CM rings.

It side-steps Reisner's criterion, shellability, Alexander duality, and
the general SR equivalence `K[Δ] CM ⟺ Δ CM`.

## Lean-target summary (the concrete F2 worklist)

- **L1**: `R[s_U⁻¹] ≅ (K[W] / I(Γ_G|_W)) ⊗_K K[U][s_U⁻¹]` with the explicit
  generator formula of Step 1.
- **L2**: localising L1 at `p`.
- **L3**: one-sided survivors isolated in `Γ_G|_W`. **Already formalised.**
- **L4**: `K[W] / I(Γ_G|_W) ≅ A^red_{G'} ⊗_K K[Λ]` with the explicit
  generator formula of Step 3.
- **L5**: reduced HH at augmentation is CM. **Already formalised**
  (`isCohenMacaulayLocalRing_reducedHH_at_augIdeal`).
- **L6 / L7 replacement**: the Q6 tensor-polynomial-localisation CM lemma,
  using `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing` + CM-localises.

The key conceptual point: **localise the reduced HH factor at its augmentation
first**, then the tensor product is merely a localisation of a polynomial ring
over a CM ring — which we already have.
