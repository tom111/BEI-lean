import BEI.Equidim
import BEI.GroebnerDeformation

/-!
# Proposition 1.6 (Herzog et al. 2010) — paper-faithful Cohen–Macaulay statement

This file assembles the paper-faithful Cohen–Macaulay statement of Proposition 1.6
from Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010):

> If `G` is a connected closed graph on `[n]` satisfying the transitivity condition
> (iii) of the paper, then `K[x, y] ⧸ J_G` is Cohen–Macaulay.

The monomial side is completed: `monomialInitialIdeal_isCohenMacaulay` in
`BEI/Equidim.lean` gives that the quotient by the monomial initial ideal of `J_G`
is Cohen–Macaulay under the Herzog–Hibi conditions. For closed graphs,
`initialIdeal_closed_eq` identifies that monomial ideal with the actual initial
ideal `span(lt(J_G))`.

The remaining paper-critical step is the Gröbner deformation transfer:

  `S ⧸ in_<(J_G)` Cohen–Macaulay  ⟹  `S ⧸ J_G` Cohen–Macaulay.

This step is the content of Eisenbud, *Commutative Algebra with a View Toward
Algebraic Geometry*, Theorem 15.17, and is proved classically via a flat
one-parameter family over `𝔸¹_K` degenerating `J_G` to `in_<(J_G)` combined with
lower semicontinuity of depth on flat families.

That infrastructure is currently absent from both Mathlib and this repository.
We therefore state the narrow BEI-shaped transfer theorem as
`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` with a single explicit `sorry`.
This is the **one** remaining paper-critical sorry in the Proposition 1.6 chain;
every other step is proved. A detailed route to closing it is tracked in
`guides/work_packages/GROEBNER_CM_TRANSFER.md` (route R1).

Once `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` is proved, Proposition 1.6
follows immediately from Step 1 via `proposition_1_6`.

## Reference: Herzog et al. (2010), Proposition 1.6 (`cmbinomial`)
-/

open MvPolynomial SimpleGraph

/--
**Gröbner deformation transfer for the binomial edge ideal.**

Under the assumption that `G` is closed — so that
`monomialInitialIdeal G = in_<(J_G)` via `initialIdeal_closed_eq` — Cohen–Macaulayness
transfers from the initial-ideal quotient back to the binomial edge ideal quotient.

Classical proof: the flat family over `𝔸¹_K` with `I_t = t^N · (t-1)-homogenization`
degenerates `J_G` to `in_<(J_G)`; depth is lower semicontinuous on flat families
over `K[t]`, so CM of the special fiber (`t = 0`) implies CM of the generic fiber
(`t = 1`). See Eisenbud, *Commutative Algebra with a View Toward Algebraic
Geometry*, Theorem 15.17.

**Status**: factored through `BEI/GroebnerDeformation.lean`. The proof reduces
to `groebnerDeformation_cm_transfer`, whose two remaining sub-sorries are
flatness of `S[t] ⧸ Ĩ` over `K[t]` and graded local-to-global CM at the
deformation's irrelevant ideal. See
`guides/work_packages/GROEBNER_CM_TRANSFER.md` (route R1) for the chain.

The narrow `K : Type` universe restriction is inherited from the HH-side CM
theorem, which is currently universe-monomorphic because of the polynomial-away
tensor API used in its proof. -/
theorem binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm
    {K : Type} [Field K] {n : ℕ} {G : SimpleGraph (Fin n)}
    (_hClosed : IsClosedGraph G)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) :=
  groebnerDeformation_cm_transfer hCM

/--
**Proposition 1.6 (Herzog–Hibi–Hreinsdóttir–Kahle–Rauh, 2010).**

Let `G` be a connected closed graph on `[n]` (with `n ≥ 2`) satisfying the
transitivity condition of Proposition 1.6: whenever `{i, j+1}` and `{j, k+1}` are
edges with `i < j < k`, the edge `{i, k+1}` is also present. Then the binomial
edge ideal quotient `K[x, y] ⧸ J_G` is Cohen–Macaulay.

Proof:

1. `prop_1_6_herzogHibi` translates the hypotheses into the Herzog–Hibi
   conditions `(i)`, `(ii)`, `(iii)` on the associated bipartite graph `Γ`.
2. `monomialInitialIdeal_isCohenMacaulay` (Step 1) shows that
   `K[x, y] ⧸ monomialInitialIdeal G` is Cohen–Macaulay under those conditions,
   via the y-shift to `Γ` and the HH bipartite CM theorem.
3. `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` (Step 2, the Gröbner
   deformation step — currently a `sorry`) transfers CM back from the initial
   ideal to `J_G`.

The `K : Type` restriction is inherited from the HH-side CM theorem. -/
theorem proposition_1_6
    {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  have hHH : HerzogHibiConditions n G := prop_1_6_herzogHibi n G hConn hClosed hCond
  have hInCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G) :=
    monomialInitialIdeal_isCohenMacaulay hn hHH
  exact binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm hClosed hInCM
