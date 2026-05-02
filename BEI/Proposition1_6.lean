import BEI.Equidim
import BEI.GroebnerDeformation
import BEI.PrimeDecompositionDimension
import BEI.Prop1_6Equidim

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

The final paper-critical step is the Gröbner deformation transfer:

  `S ⧸ in_<(J_G)` Cohen–Macaulay  ⟹  `S ⧸ J_G` Cohen–Macaulay.

This step is the content of Eisenbud, *Commutative Algebra with a View Toward
Algebraic Geometry*, Theorem 15.17, and is proved classically via a flat
one-parameter family over `𝔸¹_K` degenerating `J_G` to `in_<(J_G)` combined with
lower semicontinuity of depth on flat families.

That step is now formalized in `BEI/GroebnerDeformation.lean` as
`groebnerDeformation_cm_transfer`, using the weighted deformation over `K[t]`
and the graded local-to-global CM theorem whose Case C is closed via the
finite-free parameter-subring route in `toMathlib/GradedFiniteFree.lean` and
`toMathlib/GradedRegularSop.lean`.

The narrow BEI-shaped transfer theorem
`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` is therefore fully proved, and
Proposition 1.6 follows immediately from the monomial-side theorem.

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

**Status**: proved in `BEI/GroebnerDeformation.lean` as
`groebnerDeformation_cm_transfer`. The transfer uses flatness of `S[t] ⧸ Ĩ`
over `K[t]`, specialization at `t = 0` and `t = 1`, and the now-closed graded
local-to-global CM theorem from `toMathlib/GradedCM.lean`.

The narrow `K : Type` universe restriction is inherited from the HH-side CM
theorem, which is currently universe-monomorphic because of the polynomial-away
tensor API used in its proof. -/
theorem binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm
    {K : Type} [Field K] {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) :=
  groebnerDeformation_cm_transfer hClosed hCM

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
   deformation step) transfers CM back from the initial
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

/-- **Paper-faithful dimension formula, Corollary 3.4 specialised to Prop 1.6
graphs**: for a connected closed graph `G` on `[n]` satisfying the Prop 1.6
transitivity condition, `dim K[x, y] ⧸ J_G = n + 1`.

Proof: `prop_1_6_equidim` gives the local equidimensional surrogate;
`corollary_3_4_equidim` then yields the dimension formula
`dim = Fintype.card V + componentCount G ∅`; and for a connected graph the
component count is `1`. -/
theorem proposition_1_6_dim_formula
    {K : Type} [Field K] {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)}
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) =
    ↑(n + 1) := by
  have hEq : IsEquidim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) :=
    prop_1_6_equidim (K := K) n hn G hConn hClosed hCond
  have hDim := corollary_3_4_equidim (K := K) G hEq
  have hc : componentCount G ∅ = 1 := by
    rw [componentCount_empty]
    haveI := hConn.preconnected.subsingleton_connectedComponent
    exact Nat.card_of_subsingleton (G.connectedComponentMk hConn.nonempty.some)
  rw [hDim, hc]
  simp [Fintype.card_fin]

/-! ## Concrete examples -/

/-- The standard path graph on `Fin n` satisfies the Proposition 1.6 transitivity
condition vacuously: for `i < j`, the hypothesis `Adj i (j+1)` already forces
`i = j` or `i = j + 2`, both impossible. -/
theorem pathGraph_satisfiesProp1_6Condition (n : ℕ) :
    SatisfiesProp1_6Condition n (pathGraph n) := by
  intro i j k _ _ hij _ hadj _
  rw [SimpleGraph.pathGraph_adj] at hadj
  have hij_val : i.val < j.val := hij
  exfalso
  rcases hadj with h | h <;> (simp at h; omega)

/-- **Corollary**: for the path graph on `Fin n` with `n ≥ 2`, the binomial edge
ideal quotient `K[x, y] ⧸ J_{P_n}` is Cohen–Macaulay. (Example 1.7(b) in the
paper, via Proposition 1.6.) -/
theorem pathGraph_binomialEdgeIdeal_isCohenMacaulay
    {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        binomialEdgeIdeal (K := K) (pathGraph n)) := by
  -- Rewrite `n = (n - 1) + 1` to invoke `pathGraph_connected`.
  have hn' : n = (n - 1) + 1 := by omega
  have hConn : (pathGraph n).Connected := by
    rw [hn']; exact SimpleGraph.pathGraph_connected _
  exact proposition_1_6 hn hConn
    (pathGraph_isClosedGraph n)
    (pathGraph_satisfiesProp1_6Condition n)

/-- **Dimension formula for the path graph**: `dim K[x, y] ⧸ J_{P_n} = n + 1`.
Axiom-clean. -/
theorem pathGraph_binomialEdgeIdeal_ringKrullDim
    {K : Type} [Field K] {n : ℕ} (hn : 0 < n) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        binomialEdgeIdeal (K := K) (pathGraph n)) =
    ↑(n + 1) := by
  have hn' : n = (n - 1) + 1 := by omega
  have hConn : (pathGraph n).Connected := by
    rw [hn']; exact SimpleGraph.pathGraph_connected _
  exact proposition_1_6_dim_formula hn hConn
    (pathGraph_isClosedGraph n)
    (pathGraph_satisfiesProp1_6Condition n)
