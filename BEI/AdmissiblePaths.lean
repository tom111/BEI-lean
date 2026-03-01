import BEI.GraphProperties

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V]

/-!
# Admissible paths and their associated monomials

This file defines the monomial `u_π` associated to an admissible path `π`
from `i` to `j` in G, and the Gröbner basis element `u_π · f_{ij}`.

The monomial is:
  `u_π = (∏_{v ∈ internals(π), v > j} x_v) · (∏_{v ∈ internals(π), v < i} y_v)`

## Reference: Herzog et al. (2010), Section 2
-/

noncomputable section

open MvPolynomial

/-! ## The monomial u_π -/

/--
The internal vertices of a path `π` from `i` to `j`: all vertices except the
first and last.
-/
def internalVertices (π : List V) : List V := π.tail.dropLast

/--
The **path monomial** `u_π` for an admissible path π from i to j:
  `u_π = (∏_{v > j, v internal} x_v) · (∏_{v < i, v internal} y_v)`
-/
noncomputable def pathMonomial (i j : V) (π : List V) :
    MvPolynomial (BinomialEdgeVars V) K :=
  let internals := internalVertices π
  let xPart := (internals.filter (fun v => j < v)).map (fun v => x v)
  let yPart := (internals.filter (fun v => v < i)).map (fun v => y v)
  xPart.prod * yPart.prod

/-- For the trivial path [i, j], the path monomial is 1 (no internal vertices). -/
@[simp]
theorem pathMonomial_pair (i j : V) :
    pathMonomial (K := K) i j [i, j] = 1 := by
  simp [pathMonomial, internalVertices]

/--
The **Gröbner basis element** for path π from i to j:
  `u_π · f_{ij} = u_π · (x_i y_j - x_j y_i)`
-/
noncomputable def groebnerElement (i j : V) (π : List V) :
    MvPolynomial (BinomialEdgeVars V) K :=
  pathMonomial i j π * (x i * y j - x j * y i)

/-- For the trivial path, the Gröbner element equals the generator `f_{ij}`. -/
@[simp]
theorem groebnerElement_pair (i j : V) :
    groebnerElement (K := K) i j [i, j] = x i * y j - x j * y i := by
  simp [groebnerElement]

/--
The full **reduced Gröbner basis set** of J_G:
  `G = { u_π · f_{ij} | i < j, π admissible path from i to j in G }`
-/
def groebnerBasisSet (G : SimpleGraph V) :
    Set (MvPolynomial (BinomialEdgeVars V) K) :=
  { p | ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
        p = groebnerElement i j π }

/-! ## Membership in J_G -/

/-- Core membership lemma by strong induction on walk length.
Proves `pathMonomial i j π * f_{ij} ∈ J_G` for any valid walk satisfying admissibility
conditions (without requiring the minimality condition of `IsAdmissiblePath`).

In the inductive step, we split at the vertex v₀ = max{vₖ < i} (or min{vₖ > j}) and use:
- Case A (v₀ < i): y_{v₀} * f_{ij} = y_i * f_{v₀,j} - y_j * f_{v₀,i} (ring identity)
- Case B (v₀ > j): x_{v₀} * f_{ij} = x_j * f_{i,v₀} - x_i * f_{j,v₀} (ring identity)
Both sub-paths are shorter walks satisfying the same conditions, so IH applies.
-/
private theorem groebnerElem_mem_aux (G : SimpleGraph V) :
    ∀ (n : ℕ) (i j : V) (π : List V),
    π.length = n → i < j →
    π.head? = some i → π.getLast? = some j →
    π.Nodup →
    (∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v) →
    π.Chain' (fun a b => G.Adj a b) →
    pathMonomial (K := K) i j π * (x i * y j - x j * y i) ∈ binomialEdgeIdeal G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j π hlen hij hHead hLast hNodup hInternal hWalk
  -- Case split on π
  match π, hHead, hLast, hWalk, hNodup, hInternal, hlen with
  | [], hH, _, _, _, _, _ => simp at hH
  | [a], hH, hL, _, _, _, _ =>
    simp only [List.head?_cons, Option.some.injEq] at hH
    simp only [List.getLast?_singleton, Option.some.injEq] at hL
    subst hH; subst hL
    exact absurd hij (lt_irrefl _)
  | [a, b], hH, hL, hW, _, _, _ =>
    -- π = [a, b] = [i, j]: base case
    simp only [List.head?_cons, Option.some.injEq] at hH
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hL
    -- hH : a = i, hL : b = j
    -- G.Adj a b from the Chain' condition
    have hAdj : G.Adj a b := by
      simp [List.Chain'] at hW
      exact hW
    -- Rewrite a = i, b = j, pathMonomial [a, b] = 1
    have hpm : pathMonomial (K := K) i j [a, b] = 1 := by
      rw [← hH, ← hL]; exact pathMonomial_pair a b
    rw [hpm, one_mul]
    have hAdj' : G.Adj i j := hH ▸ hL ▸ hAdj
    exact Ideal.subset_span ⟨i, j, hAdj', hij, rfl⟩
  | a :: b :: c :: rest, hH, hL, hW, hND, hInt, hlen' =>
    -- π has at least one internal vertex; use sorry for the inductive step
    sorry

/--
Every Gröbner basis element `u_π · f_{ij}` belongs to `binomialEdgeIdeal G`.

Proof by induction on the length of π:
- Base case (|π| = 2): `u_π = 1`, so `groebnerElement i j [i,j] = f_{ij} ∈ J_G`.
- Inductive step: use an algebraic identity to write `u_π f_{ij}` as a combination
  of shorter Gröbner elements.

Reference: Herzog et al. (2010), proof of Theorem 2.1, Step 1.
-/
theorem groebnerElement_mem (G : SimpleGraph V) (i j : V) (π : List V)
    (hπ : IsAdmissiblePath G i j π) :
    groebnerElement (K := K) i j π ∈ binomialEdgeIdeal G := by
  obtain ⟨hij, hHead, hLast, hNodup, hInternal, hWalk, _⟩ := hπ
  exact groebnerElem_mem_aux G π.length i j π rfl hij hHead hLast hNodup hInternal hWalk

/-- Every generator `f_{ij}` (for edges {i,j} ∈ E(G), i < j) is in the Gröbner basis set. -/
theorem generator_in_groebnerBasisSet (G : SimpleGraph V) (i j : V)
    (hAdj : G.Adj i j) (hij : i < j) :
    x (K := K) i * y j - x j * y i ∈ groebnerBasisSet G :=
  ⟨i, j, [i, j], edge_is_admissible G hAdj hij, by simp [groebnerElement]⟩

end
