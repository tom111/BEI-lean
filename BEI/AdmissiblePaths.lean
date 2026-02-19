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
  sorry

/-- Every generator `f_{ij}` (for edges {i,j} ∈ E(G), i < j) is in the Gröbner basis set. -/
theorem generator_in_groebnerBasisSet (G : SimpleGraph V) (i j : V)
    (hAdj : G.Adj i j) (hij : i < j) :
    x (K := K) i * y j - x j * y i ∈ groebnerBasisSet G :=
  ⟨i, j, [i, j], edge_is_admissible G hAdj hij, by simp [groebnerElement]⟩

end
