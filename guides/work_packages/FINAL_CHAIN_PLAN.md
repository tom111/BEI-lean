# Plan: Close the HH `p ⊄ m⁺` sorry — final chain

## Context

The F2 route to Proposition 1.6 CM at non-augmentation primes has landed
six of seven pieces:

| Piece | Status | Name / location |
|---|---|---|
| L3 (one-sided survivors isolated) | ✓ done | `hhSurvivor_{x,y}_isolated` |
| L4 (surviving-graph decomposition) | ✓ done | `L4Iso`, `BEI/Equidim.lean` |
| L5 (reduced HH at aug is CM) | ✓ done — but **wrong form** | `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` |
| L6 (polynomial-away tensor merge) | ✓ done | `polynomialAwayTensorEquiv` |
| L7 replacement (tensor-poly-loc CM) | ✓ done | `isCohenMacaulayRing_tensor_away` |
| L1 (monomial-localisation iso) | ✓ done | `L1Iso`, `BEI/Equidim.lean` |
| **Final chain** | pending | `BEI/Equidim.lean:6723` |

The sole remaining sorry is the `p ⊄ m⁺` branch of
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`. The
chain would compose L1 → L4 → L6 → L7 replacement to conclude CM —
except that the L7 replacement asks for a globally-CM `A`, and the
only CM fact we currently have about `reducedHHRing G'` is the L5
statement for the **full** HH ring of the original graph `G`, not
for the abstract reduced HH ring of the smaller graph `G'`.

## The L5 form mismatch

L5 (currently formalised) proves

    QuotSMulTop (mk y_last)
      ((Localization.AtPrime (augIdeal G) R_G) ⧸ span{x_last})
    is Cohen–Macaulay local

where `R_G = MvPolynomial σ K ⧸ bipartiteEdgeMonomialIdeal G` for
the **original** graph `G` on `Fin n`.

What the final chain needs is

    Localization.AtPrime (augIdealReduced G')
      (reducedHHRing G')
    is Cohen–Macaulay local

for the **abstract** reduced HH ring of the smaller graph `G'`
(`= smallerHHGraph G U`, on `Fin (r + 1)` with `r = pairedCount G U`).

The bridge between these two forms is the trailing-pair decomposition

    R_G  ≃ₐ[K]  reducedHHRing G  ⊗_K  MvPolynomial (Fin 2) K

This iso exists because `bipartiteEdgeMonomialIdeal G` has no
generator involving `x_{n-1}` or `y_{n-1}` — an edge of `hhEdgeSet`
requires `i ≤ j, j+1 < n`, so `i, j < n-1`, and neither last-index
variable appears as an endpoint.

## Proposed three-session plan

### Session A — trailing-pair iso and L5 transport (~150–250 LOC)

**Goal**: prove, for any HH graph `G` on `Fin (r + 1)` with `r + 1 ≥ 2`,
that `Localization.AtPrime (augIdealReduced G) (reducedHHRing G)` is
Cohen–Macaulay local.

**Location**: `BEI/ReducedHH.lean` (augmenting the abstract reduced HH
infrastructure) OR a new `BEI/ReducedHHIsom.lean` if the Session-A
content is large enough to merit separation.

**Deliverables**:

1. **`R_G ≅ reducedHHRing G ⊗_K MvPolynomial (Fin 2) K`** — a `K`-algebra
   iso. Constructed via `MvPolynomial.sumAlgEquiv`-style decompositions:
   - `BinomialEdgeVars (Fin (r+1)) ≃ BinomialEdgeVars (Fin r) ⊕ Fin 2`
     (where `Fin 2` indexes `(x_last, y_last)`).
   - `MvPolynomial (A ⊕ B) K ≃ₐ[K] MvPolynomial A K ⊗_K MvPolynomial B K`
     (via Mathlib's tensor-polynomial identifications).
   - The bipartiteEdgeMonomialIdeal on `σ` factors through the σ' side
     (no last-pair involvement), so the quotient descends cleanly.

2. **Transported L5**: combine the trailing-pair iso with the existing
   `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` to conclude CM of
   `Localization.AtPrime (augIdealReduced G) (reducedHHRing G)` for any
   HH graph `G` on `Fin (r + 1)` with `r ≥ 1`.

3. **Base case `r = 0`**: `reducedHHRing G` is `MvPolynomial (Fin 0) K = K`;
   `augIdealReduced G = ⊥`; `Localization.AtPrime ⊥ K = K`, which is CM
   local trivially. Handle with `isCohenMacaulayLocalRing_of_isField`.

**Risk**: moderate. The `BinomialEdgeVars (Fin (r+1)) ≃ BinomialEdgeVars (Fin r) ⊕ Fin 2` iso looks easy but needs care with index arithmetic. The quotient-through-tensor step may need a small lemma.

### Session B — promote local CM to global CM of the tensor factor (~50–100 LOC)

**Goal**: prove that `Localization.AtPrime (augIdealReduced G) (reducedHHRing G)`, which is a CM local ring by Session A, is also **globally** Cohen–Macaulay (as an `IsCohenMacaulayRing`).

**Location**: `BEI/ReducedHH.lean` or `BEI/Equidim.lean` (wherever Session A lands).

**Deliverables**:

- Apply `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` (already in
  `toMathlib/CohenMacaulay/Localization.lean:761`) to Session A's
  conclusion. This should be near-mechanical — ~10–20 LOC once the
  prerequisites are in scope.

**Risk**: low.

### Session C — final chain composition (~200–400 LOC)

**Goal**: close the sorry at `BEI/Equidim.lean:6723`.

**Strategy**:

1. Given `p : Ideal R` with `¬ p ≤ augIdeal G`, define
   `U : Finset (BinomialEdgeVars (Fin n))` as unit variables at `p`.
   Prove `U` is independent in `Γ_G` (via primality: any edge among
   units would force one unit to be zero in `R_p`, contradicting
   non-membership in `p`).

2. Compose the ring equivalences into a single `RingEquiv` from
   `Localization.AtPrime p R` to the target CM ring:

   - `R_p ≅ (R[mkI s_U⁻¹])_{p'}` via
     `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`
     (possible because `mkI s_U ∉ p`).

   - `R[mkI s_U⁻¹] ≅ restrictedHHRing G W ⊗_K Localization.Away s_U^U`
     via `L1Iso`.

   - `restrictedHHRing G W ≅ reducedHHRing G' ⊗_K MvPolynomial Λ K`
     via `L4Iso`.

   - Combine the rightmost two tensor factors via
     `polynomialAwayTensorEquiv` (L6):
     `MvPolynomial Λ K ⊗_K Localization.Away s_U^U ≃ₐ[K]
      Localization.Away (rename Sum.inr s_U^U : MvPolynomial (Λ ⊔ U) K)`.

   - Transport through `Algebra.TensorProduct.congr` or explicit
     `AlgEquiv.trans`:
     `R[mkI s_U⁻¹] ≅ reducedHHRing G' ⊗_K Localization.Away (something on Λ ⊔ U)`.

3. Localise further and split: the inner prime `p'` pulls back through
   the tensor to give primes on each factor. Use CM-localises to
   reduce to showing the global ring is CM.

4. Apply L7 replacement with
   `A := Localization.AtPrime (augIdealReduced G') (reducedHHRing G')`
   (globally CM by Session A + B) and `τ := Λ ⊔ U`, `s := rename s_U^U`:
   `A ⊗_K Localization.Away s` is globally CM.

5. `Localization.AtPrime p' (A ⊗_K ...)` is CM by
   `IsCohenMacaulayRing.CM_localize`.

6. Transport CM back to `Localization.AtPrime p R` via the composed
   RingEquiv using `isCohenMacaulayLocalRing_of_ringEquiv'`.

**Subtleties**:

- Aligning the tensor `(reducedHHRing G') ⊗_K (MvPolynomial Λ K ⊗_K
  Localization.Away s_U^U)` with the L7-replacement hypothesis shape
  `A ⊗_K Localization.Away s` requires `Algebra.TensorProduct.assoc`.
- The prime `𝔓` in the target tensor ring needs to be produced
  explicitly — it is the image of `p` under the composed iso.
- Base case `r = 0`: the reduced HH factor vanishes (`reducedHHRing G' = K`),
  and the whole chain simplifies to `R_p ≅ (K ⊗_K Localization.Away ...)_𝔓
  ≅ Localization.Away...`, which is a localisation of a polynomial ring
  over `K` (CM). Handle as a `by_cases r = 0` split at the start of
  Session C.

**Risk**: moderate to high due to tensor-associativity bookkeeping
and prime transport across multiple isos.

### Total effort

- Session A: ~150–250 LOC (moderate risk).
- Session B: ~50–100 LOC (low risk).
- Session C: ~200–400 LOC (moderate-high risk).
- **Total**: ~400–750 LOC.

## Execution order

Strongly recommend:
1. Session A first (enables B).
2. Session B (trivial once A lands).
3. Session C last (consumes A + B).

Each session builds cleanly on its predecessor; no interleaving
required.

## Open questions for the thinking model

The following questions would confirm no hidden obstructions before
committing engineering effort. Consider attaching this plan document
when asking.

1. **Trailing-pair iso form**: is
   `R_G ≅ reducedHHRing G ⊗_K MvPolynomial (Fin 2) K` exactly right,
   or does the iso have a subtly different form (e.g. the HH ideal
   restricted to σ' coincides with our `reducedHHIdeal` only up to a
   relabelling)? In particular: our `reducedHHEdgeSet G` for
   `G : SimpleGraph (Fin (r + 1))` asks for
   `G.Adj a.castSucc ⟨b.val + 1, hb⟩` with `0 ≤ a ≤ b < r`, variables
   on `BinomialEdgeVars (Fin r)`. The "σ' bipartite edge set" from
   cutting out the last pair of the full HH on `Fin (r + 1)` asks for
   `G.Adj i ⟨j.val + 1, hj⟩` with `i ≤ j`, `j.val + 1 < r + 1`,
   variables on `BinomialEdgeVars (Fin r)` after discarding index r.
   These look equal, but the exact identification may need spelling
   out. Please confirm.

2. **Alternative to Session A**: is there a conceptually cleaner way
   to prove `Localization.AtPrime (augIdealReduced G) (reducedHHRing G)`
   is CM local — e.g., directly recurse on the main theorem (treating
   the main theorem itself as inductive on `n`), or a non-obvious
   shortcut using the L5 statement as-is without going through the
   trailing-pair iso?

3. **Prime transport in Session C**: the chain hops across 4–5 ring
   equivalences, each potentially changing the prime. Is there a
   clean way to bundle this — e.g., a single "factor through all the
   isos and localise at the end" recipe — or is per-iso comap
   necessary?

4. **Base case `r = 0`**: is there a risk that the chain construction
   silently fails when `pairedSurvivors G U = ∅` (e.g., a tensor with
   `reducedHHRing` on `Fin 0`, which is `K`, triggering some implicit
   definitional issue)? Are there edge cases worth anticipating?

5. **Any other obstruction** we haven't considered — e.g., whether
   the `Finite` / `DecidableEq` hypotheses of the L7 replacement play
   cleanly with the `Λ ⊔ U` index type obtained after merging?
