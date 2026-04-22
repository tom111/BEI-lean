import BEI.Equidim
import BEI.Radical
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Algebra.MvPolynomial.Equiv
import toMathlib.GradedQuotient
import toMathlib.GradedCM

/-!
# Gröbner deformation of the binomial edge ideal (Route R1, framework)

This file lays down the structural framework for proving Eisenbud 15.17 in
the BEI setting. The classical Gröbner deformation of `J_G` to its monomial
initial ideal is realized as a one-parameter family `S[t] ⧸ Ĩ` over `K[t]`
with:

- generic fiber (`t = 1`): `S ⧸ J_G`;
- special fiber (`t = 0`): `S ⧸ monomialInitialIdeal G`.

Under a positive-weight grading on `S[t]` that makes each deformed generator
weighted-homogeneous, `S[t] ⧸ Ĩ` is a connected ℕ-graded `K`-algebra. The
classical proof of CM transfer is then a four-arrow chain:

```text
S ⧸ in_<(J_G) CM   ──(regular-quotient lift)──▶  S[t] ⧸ Ĩ CM at irrelevant
                   ──(graded local-to-global)──▶ S[t] ⧸ Ĩ CM globally
                   ──(flatness ⇒ t-1 regular)──▶ t-1 regular on S[t] ⧸ Ĩ
                   ──(regular-quotient descent)─▶ S ⧸ J_G CM
```

This file builds the framework of the chain. The two paper-faithful sub-sorries
are isolated:

- `tildeJ_isFlat_over_polyT`: flatness of the deformation over `K[t]`.
- `tildeJ_isCohenMacaulayLocalRing_at_irrelevant`: local CM at the irrelevant
  ideal of `S[t] ⧸ Ĩ`. (Follows from Step 1 + the regular-quotient lift, but
  needs the homogeneous-prime branch of `toMathlib/GradedCM.lean` to descend
  to global CM, with one Case-C dependency.)

The high-level theorem `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`
(originally a single sorry in `BEI/Proposition1_6.lean`) is now factored
through these two sub-sorries via the chain.

## Reference: Herzog et al. (2010), Proposition 1.6; Eisenbud (1995), Thm 15.17.
-/

noncomputable section

open MvPolynomial SimpleGraph

variable {K : Type} [Field K]

/-! ## The deformation ring and its specialization maps -/

/-- Opaque type synonym for the deformation variable type.

    Defined as `def` (not `abbrev`) to prevent Lean's typeclass resolution from
    finding `Sum.instLTSum` / `Sum.instLESum` (which use `Sum.LiftRel`, a
    product ordering) when searching for `LT` / `LE` on the deformation
    variable type. This avoids an instance diamond with our custom
    `defVars_LinearOrder` below, just as `BinomialEdgeVars` does for `V ⊕ V`. -/
def DefVars (n : ℕ) : Type := BinomialEdgeVars (Fin n) ⊕ Unit

instance (n : ℕ) : DecidableEq (DefVars n) :=
  inferInstanceAs (DecidableEq (BinomialEdgeVars (Fin n) ⊕ Unit))

instance (n : ℕ) : Finite (DefVars n) :=
  inferInstanceAs (Finite (BinomialEdgeVars (Fin n) ⊕ Unit))

/-- The deformation ring `S[t] = K[x, y, t]` for the BEI Gröbner deformation of
    `J_G ⊂ MvPolynomial (BinomialEdgeVars (Fin n)) K`. Variables:

    - `Sum.inl (Sum.inl i)` is `x_i` for `i : Fin n`;
    - `Sum.inl (Sum.inr j)` is `y_j` for `j : Fin n`;
    - `Sum.inr ()` is the deformation parameter `t`. -/
abbrev DefRing (n : ℕ) (K : Type) [Field K] : Type :=
  MvPolynomial (DefVars n) K

/-- The deformation parameter `t ∈ S[t]`. -/
def tDef (n : ℕ) : DefRing n K := X (Sum.inr ())

/-- The base inclusion `S → S[t]` sending each `BinomialEdgeVars` variable to
    its image under `Sum.inl`. -/
def baseInclude (n : ℕ) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K →ₐ[K] DefRing n K :=
  rename Sum.inl

/-- Specialization at `t = 0`: the `K`-algebra map `S[t] →ₐ[K] S` sending
    `t ↦ 0` and each base variable to itself. -/
def specZero (n : ℕ) : DefRing n K →ₐ[K] MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  aeval (Sum.elim X (fun _ => 0))

/-- Specialization at `t = 1`: the `K`-algebra map `S[t] →ₐ[K] S` sending
    `t ↦ 1` and each base variable to itself. -/
def specOne (n : ℕ) : DefRing n K →ₐ[K] MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  aeval (Sum.elim X (fun _ => 1))

@[simp] lemma specZero_X_inl (n : ℕ) (v : BinomialEdgeVars (Fin n)) :
    specZero (K := K) n (X (Sum.inl v)) = X v := by
  change aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specZero_X_inr (n : ℕ) (u : Unit) :
    specZero (K := K) n (X (Sum.inr u)) = 0 := by
  change aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specOne_X_inl (n : ℕ) (v : BinomialEdgeVars (Fin n)) :
    specOne (K := K) n (X (Sum.inl v)) = X v := by
  change aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specOne_X_inr (n : ℕ) (u : Unit) :
    specOne (K := K) n (X (Sum.inr u)) = 1 := by
  change aeval _ _ = _; rw [aeval_X]; rfl

/-! ## Deformed generators and the deformation ideal -/

/-- The deformed binomial generator
    `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i ∈ S[t]`.

    The `t^(j-i)` exponent is chosen so that `f̃_{i,j}` is weighted-homogeneous
    under the weight `w(x_i) = 2(n+1-i)`, `w(y_j) = (n+1-j)`, `w(t) = 1`,
    making `S[t] ⧸ Ĩ` a connected ℕ-graded `K`-algebra. -/
def fijTilde {n : ℕ} (i j : Fin n) : DefRing n K :=
  X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j)) -
    (X (Sum.inr ()))^(j.val - i.val) *
      X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))

/-- The Gröbner deformation ideal:
    `Ĩ = ⟨f̃_{i,j} : {i, j} ∈ E(G), i < j⟩ ⊂ S[t]`.

    Specialization at `t = 1` recovers `J_G`; specialization at `t = 0`
    recovers `monomialInitialIdeal G`. -/
def tildeJ {n : ℕ} (G : SimpleGraph (Fin n)) : Ideal (DefRing n K) :=
  Ideal.span { p | ∃ i j : Fin n, G.Adj i j ∧ i < j ∧ p = (fijTilde i j : DefRing n K) }

/-! ## Specialization of the deformed generator -/

lemma specOne_fijTilde {n : ℕ} (i j : Fin n) :
    specOne (K := K) n (fijTilde i j) = x (K := K) i * y j - x j * y i := by
  change specOne (K := K) n (X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j)) -
    X (Sum.inr ()) ^ (j.val - i.val) *
      X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))) = _
  rw [map_sub, map_mul, map_mul, map_mul, map_pow,
    specOne_X_inl, specOne_X_inl, specOne_X_inl, specOne_X_inl, specOne_X_inr]
  simp [x, y]

lemma specZero_fijTilde {n : ℕ} (i j : Fin n) (hij : i < j) :
    specZero (K := K) n (fijTilde i j) =
      (x (K := K) i * y j : MvPolynomial (BinomialEdgeVars (Fin n)) K) := by
  have hpos : 0 < j.val - i.val := by
    have := Fin.lt_def.mp hij
    omega
  have hzero : (0 : MvPolynomial (BinomialEdgeVars (Fin n)) K) ^ (j.val - i.val) = 0 :=
    zero_pow (Nat.pos_iff_ne_zero.mp hpos)
  change specZero (K := K) n (X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j)) -
    X (Sum.inr ()) ^ (j.val - i.val) *
      X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))) = _
  rw [map_sub, map_mul, map_mul, map_mul, map_pow,
    specZero_X_inl, specZero_X_inl, specZero_X_inl, specZero_X_inl, specZero_X_inr,
    hzero, zero_mul, zero_mul, sub_zero]
  rfl

/-! ## Fiber identification (R1.e) -/

/-- The `t = 1` fiber: pushing `Ĩ` forward along `specOne` gives `J_G`. -/
theorem tildeJ_specOne_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal.map (specOne (K := K) n).toRingHom (tildeJ G) = binomialEdgeIdeal G := by
  unfold tildeJ binomialEdgeIdeal
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, j, hadj, hij, rfl⟩, rfl⟩
    refine ⟨i, j, hadj, hij, ?_⟩
    change specOne n (fijTilde i j) = _
    exact specOne_fijTilde i j
  · rintro ⟨i, j, hadj, hij, rfl⟩
    refine ⟨fijTilde i j, ⟨i, j, hadj, hij, rfl⟩, ?_⟩
    change specOne n (fijTilde i j) = _
    exact specOne_fijTilde i j

/-- The `t = 0` fiber: pushing `Ĩ` forward along `specZero` gives the
    monomial initial ideal. -/
theorem tildeJ_specZero_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal.map (specZero (K := K) n).toRingHom (tildeJ G) = monomialInitialIdeal G := by
  unfold tildeJ monomialInitialIdeal
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, j, hadj, hij, rfl⟩, rfl⟩
    refine ⟨i, j, hadj, hij, ?_⟩
    change specZero n (fijTilde i j) = _
    rw [specZero_fijTilde i j hij]
    rfl
  · rintro ⟨i, j, hadj, hij, rfl⟩
    refine ⟨fijTilde i j, ⟨i, j, hadj, hij, rfl⟩, ?_⟩
    change specZero n (fijTilde i j) = _
    rw [specZero_fijTilde i j hij]
    rfl

/-! ## Identification of `S ⧸ J_G` with the `t = 1` quotient of `S[t] ⧸ Ĩ` -/

/-- The base inclusion `S → S[t]` followed by `mk_{Ĩ ⊔ (t-1)}` factors through
    `binomialEdgeIdeal G`. -/
lemma binomialEdgeIdeal_le_baseInclude_comap_sup
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    binomialEdgeIdeal (K := K) G ≤
      Ideal.comap (baseInclude (K := K) n).toRingHom
        (tildeJ (K := K) G ⊔ Ideal.span {tDef (K := K) n - 1}) := by
  rw [binomialEdgeIdeal, Ideal.span_le]
  rintro p ⟨i, j, hadj, hij, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  -- baseInclude (x_i y_j - x_j y_i) = X(inl(inl i)) * X(inl(inr j)) - X(inl(inl j)) * X(inl(inr i))
  -- = f̃_{i,j} + (1 - t^{j-i}) * X(inl(inl j)) * X(inl(inr i))
  -- = f̃_{i,j} + (-(t-1)) * (1 + t + ... + t^{j-i-1}) * X(inl(inl j)) * X(inl(inr i))
  -- so it lies in Ĩ + Ideal.span {t-1}
  set d := j.val - i.val
  set Xji : DefRing n K := X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))
  set Xij : DefRing n K := X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j))
  -- Identity: 1 - t^d = -(t - 1) * (∑_{k<d} t^k), via geom_sum_mul.
  have hgeom : (1 : DefRing n K) - tDef n ^ d =
      -(tDef n - 1) * (Finset.range d).sum (fun k => tDef n ^ k) := by
    have h1 : (Finset.range d).sum (fun k => tDef (K := K) n ^ k) * (tDef n - 1) =
        tDef n ^ d - 1 := geom_sum_mul (tDef (K := K) n) d
    linear_combination h1
  -- baseInclude (x_i y_j - x_j y_i) = Xij - Xji
  have hbase : (baseInclude (K := K) n).toRingHom (x (K := K) i * y j - x j * y i) =
      Xij - Xji := by
    change baseInclude (K := K) n (x i * y j - x j * y i) = _
    simp only [baseInclude, x, y, map_sub, map_mul, rename_X]
    rfl
  rw [hbase]
  -- Decompose: Xij - Xji = (Xij - t^d * Xji) + (t^d * Xji - Xji)
  --                      = f̃_{i,j} + (t^d - 1) * Xji
  --                      = f̃_{i,j} + (-(1 - t^d)) * Xji
  --                      = f̃_{i,j} - (1 - t^d) * Xji
  --                      = f̃_{i,j} + (t - 1) * Σ_{k<d} t^k * Xji
  have hfij_def : fijTilde (K := K) i j = Xij - tDef n ^ d * Xji := by
    show _ = _
    simp [fijTilde, tDef, Xij, Xji, d, mul_assoc]
  have hsplit : Xij - Xji = fijTilde (K := K) i j +
      (tDef n - 1) * ((Finset.range d).sum (fun k => tDef n ^ k)) * Xji := by
    rw [hfij_def]
    have hgeom' : (1 : DefRing n K) - tDef n ^ d +
        (tDef n - 1) * (Finset.range d).sum (fun k => tDef n ^ k) = 0 := by
      rw [hgeom]; ring
    linear_combination -hgeom' * Xji
  rw [hsplit]
  apply Ideal.add_mem
  · -- f̃_{i,j} ∈ Ĩ ⊆ Ĩ ⊔ (t-1)
    apply Ideal.mem_sup_left
    exact Ideal.subset_span ⟨i, j, hadj, hij, rfl⟩
  · -- (t-1) * (geometric sum) * Xji ∈ (t-1) ⊆ Ĩ ⊔ (t-1)
    apply Ideal.mem_sup_right
    have ht1 : (tDef (K := K) n - 1) ∈ Ideal.span {tDef (K := K) n - 1} :=
      Ideal.subset_span (Set.mem_singleton _)
    have h1 : (tDef n - 1) * (Finset.range d).sum (fun k => tDef n ^ k) ∈
        Ideal.span {tDef (K := K) n - 1} :=
      Ideal.mul_mem_right _ _ ht1
    exact Ideal.mul_mem_right _ _ h1

/-! ## The `t = 1` quotient is `S ⧸ J_G` -/

section BaseQuotEquiv

-- The iso construction below needs more elaboration budget than the default
-- because of the deeply-nested types `MvPolynomial (DefVars n) K`.
set_option linter.style.setOption false in
set_option maxHeartbeats 1200000

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Abbreviation for the target sup ideal. -/
private abbrev sumIdeal : Ideal (DefRing n K) :=
  tildeJ (K := K) G ⊔ Ideal.span {tDef (K := K) n - 1}

/-- The composition `(mk (Ĩ ⊔ {t-1})) ∘ baseInclude` vanishes on `binomialEdgeIdeal G`. -/
private lemma baseInclude_quot_vanishes (a : MvPolynomial (BinomialEdgeVars (Fin n)) K)
    (ha : a ∈ binomialEdgeIdeal (K := K) G) :
    (Ideal.Quotient.mk (sumIdeal (K := K) G)).comp (baseInclude (K := K) n).toRingHom a = 0 := by
  have h := binomialEdgeIdeal_le_baseInclude_comap_sup (K := K) G ha
  rw [Ideal.mem_comap] at h
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact h

/-- Forward map of the iso, induced by `baseInclude`. -/
def baseQuotForward :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G →+*
    DefRing n K ⧸ sumIdeal (K := K) G :=
  Ideal.Quotient.lift (binomialEdgeIdeal (K := K) G)
    ((Ideal.Quotient.mk (sumIdeal (K := K) G)).comp (baseInclude (K := K) n).toRingHom)
    (baseInclude_quot_vanishes G)

/-- The composition `(mk J_G) ∘ specOne` vanishes on the sup ideal. -/
private lemma specOne_quot_vanishes (a : DefRing n K)
    (ha : a ∈ sumIdeal (K := K) G) :
    (Ideal.Quotient.mk (binomialEdgeIdeal (K := K) G)).comp
      (specOne (K := K) n).toRingHom a = 0 := by
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [Submodule.mem_sup] at ha
  obtain ⟨i, hi, j, hj, rfl⟩ := ha
  rw [map_add]
  refine Ideal.add_mem _ ?_ ?_
  · -- specOne i ∈ Ideal.map specOne (tildeJ G) = binomialEdgeIdeal G
    have hmap : (specOne (K := K) n).toRingHom i ∈
        Ideal.map (specOne (K := K) n).toRingHom (tildeJ G) :=
      Ideal.mem_map_of_mem _ hi
    rw [tildeJ_specOne_eq] at hmap
    exact hmap
  · -- specOne(q*(t-1)) = specOne(q) * 0 = 0
    rw [Ideal.mem_span_singleton] at hj
    obtain ⟨q, rfl⟩ := hj
    have heq : (specOne (K := K) n).toRingHom ((tDef n - 1) * q) = 0 := by
      rw [map_mul, map_sub]
      change ((specOne n) (X (Sum.inr ())) - (specOne n) 1) * (specOne n) q = 0
      rw [specOne_X_inr, map_one, sub_self, zero_mul]
    rw [heq]
    exact Ideal.zero_mem _

/-- Backward map of the iso, induced by `specOne`. -/
def baseQuotBackward :
    DefRing n K ⧸ sumIdeal (K := K) G →+*
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G :=
  Ideal.Quotient.lift (sumIdeal (K := K) G)
    ((Ideal.Quotient.mk (binomialEdgeIdeal (K := K) G)).comp (specOne (K := K) n).toRingHom)
    (specOne_quot_vanishes G)

/-- `specOne ∘ baseInclude = identity` on `MvPolynomial (BinomialEdgeVars (Fin n)) K`. -/
private lemma specOne_baseInclude (p : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    (specOne (K := K) n) ((baseInclude (K := K) n) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    change (specOne n) ((baseInclude n) (C r)) = C r
    rw [show (baseInclude (K := K) n) (C r) = C r from by simp [baseInclude],
        show (specOne (K := K) n) (C r) = C r from by simp [specOne]]
  | add p q hp hq =>
    change (specOne n) ((baseInclude n) (p + q)) = p + q
    rw [map_add, map_add, hp, hq]
  | mul_X p v ih =>
    change (specOne n) ((baseInclude n) (p * X v)) = p * X v
    rw [map_mul, map_mul, ih]
    have h1 : (baseInclude (K := K) n) (X v) = X (Sum.inl v) := by
      simp [baseInclude]
    rw [h1, specOne_X_inl]

/-- Backward composed with forward equals identity (on the quotient). -/
private lemma baseQuotBackward_baseQuotForward :
    (baseQuotBackward (K := K) G).comp (baseQuotForward (K := K) G) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (Ideal.Quotient.mk (binomialEdgeIdeal G)) ((specOne n) ((baseInclude n) p)) =
      (Ideal.Quotient.mk (binomialEdgeIdeal G)) p
  rw [specOne_baseInclude]

/-- Modulo the sum ideal, every variable equals its image under
    `baseInclude ∘ specOne`. -/
private lemma quot_baseInclude_specOne_X (v : DefVars n) :
    (Ideal.Quotient.mk (sumIdeal (K := K) G))
      ((baseInclude (K := K) n) ((specOne (K := K) n) (X v))) =
    (Ideal.Quotient.mk (sumIdeal (K := K) G)) (X v) := by
  rcases v with v | u
  · -- Sum.inl v: specOne(X (Sum.inl v)) = X v, baseInclude(X v) = X (Sum.inl v).
    rw [specOne_X_inl]
    have h1 : (baseInclude (K := K) n) (X v) = X (Sum.inl v) := by simp [baseInclude]
    rw [h1]
  · -- Sum.inr u: specOne(X (Sum.inr u)) = 1, baseInclude(1) = 1.
    -- Need 1 ≡ X (Sum.inr u) (i.e. tDef n) modulo {t - 1}.
    have hu : u = () := by cases u; rfl
    subst hu
    rw [specOne_X_inr, map_one, Ideal.Quotient.eq]
    change (1 : DefRing n K) - tDef n ∈ sumIdeal G
    have hmem : (1 : DefRing n K) - tDef n = -(tDef n - 1) := by ring
    rw [hmem]
    apply (Ideal.neg_mem_iff _).mpr
    apply Ideal.mem_sup_right
    exact Ideal.subset_span (Set.mem_singleton _)

/-- Forward composed with backward equals identity (on the quotient). -/
private lemma baseQuotForward_baseQuotBackward :
    (baseQuotForward (K := K) G).comp (baseQuotBackward (K := K) G) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (Ideal.Quotient.mk (sumIdeal G))
    ((baseInclude n) ((specOne n) p)) =
      (Ideal.Quotient.mk (sumIdeal G)) p
  induction p using MvPolynomial.induction_on with
  | C r =>
    have h1 : (specOne (K := K) n) (C r) = C r := by simp [specOne]
    have h2 : (baseInclude (K := K) n) (C r) = C r := by simp [baseInclude]
    rw [h1, h2]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p v ih =>
    rw [map_mul, map_mul, map_mul, ih, quot_baseInclude_specOne_X, ← map_mul]

/-- The ring iso `MvPolynomial _ ⧸ J_G ≃+* DefRing ⧸ (Ĩ ⊔ {t-1})` induced by
    the splitting `specOne ∘ baseInclude = id`. -/
def baseQuotEquiv :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G ≃+*
    DefRing n K ⧸ sumIdeal (K := K) G :=
  RingEquiv.ofRingHom
    (baseQuotForward (K := K) G) (baseQuotBackward (K := K) G)
    (baseQuotForward_baseQuotBackward (K := K) G)
    (baseQuotBackward_baseQuotForward (K := K) G)

end BaseQuotEquiv

/-! ## The `t = 0` quotient is `S ⧸ monomialInitialIdeal G`

Parallel to `BaseQuotEquiv`, but for the `t = 0` specialization. The sum
ideal here is `tildeJ G ⊔ span{tDef n}`; modulo this, the class of `tDef n`
is zero, so `specZero` serves as the backward map and its composition with
`baseInclude` equals the identity. -/

section SpecZeroQuotEquiv

-- The iso construction below needs more elaboration budget than the default
-- because of the deeply-nested types `MvPolynomial (DefVars n) K`.
set_option linter.style.setOption false in
set_option maxHeartbeats 1200000

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Abbreviation for the `t = 0` sum ideal. -/
private abbrev zeroSumIdeal : Ideal (DefRing n K) :=
  tildeJ (K := K) G ⊔ Ideal.span {tDef (K := K) n}

/-- The generator `x_i · y_j` of `monomialInitialIdeal G` lifts into
`tildeJ G ⊔ span{tDef n}` under `baseInclude`, because

  `baseInclude (x_i y_j) = X_{inl(inl i)} · X_{inl(inr j)}`
  `                     = f̃_{i,j} + t^(j-i) · X_{inl(inl j)} · X_{inl(inr i)}`.

The first summand lies in `tildeJ G`; the second (with `j - i ≥ 1`) lies in
`span{tDef n}`. -/
lemma monomialInitialIdeal_le_baseInclude_comap_zeroSum :
    monomialInitialIdeal (K := K) G ≤
      Ideal.comap (baseInclude (K := K) n).toRingHom (zeroSumIdeal (K := K) G) := by
  rw [monomialInitialIdeal, Ideal.span_le]
  rintro p ⟨i, j, hadj, hij, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  set d := j.val - i.val
  have hd_pos : 0 < d := by
    simp only [d]; have := Fin.lt_def.mp hij; omega
  set Xji : DefRing n K := X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))
  set Xij : DefRing n K := X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j))
  -- baseInclude (X(inl i) * X(inr j)) = Xij.
  have hbase : (baseInclude (K := K) n).toRingHom
      (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars (Fin n)) K) = Xij := by
    change baseInclude (K := K) n _ = _
    simp only [baseInclude, map_mul, rename_X]
    rfl
  rw [hbase]
  -- Xij = f̃_{i,j} + tDef^d * Xji.
  have hfij_def : fijTilde (K := K) i j = Xij - tDef n ^ d * Xji := by
    change _ = _
    simp [fijTilde, tDef, Xij, Xji, d, mul_assoc]
  have hsplit : Xij = fijTilde (K := K) i j + tDef n ^ d * Xji := by
    rw [hfij_def]; ring
  rw [hsplit]
  apply Ideal.add_mem
  · apply Ideal.mem_sup_left
    exact Ideal.subset_span ⟨i, j, hadj, hij, rfl⟩
  · apply Ideal.mem_sup_right
    -- `tDef n ^ d` is divisible by `tDef n` since `d ≥ 1`.
    have hpow : tDef (K := K) n ^ d = tDef n * tDef n ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow, mul_assoc]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.subset_span (Set.mem_singleton _)

/-- The composition `(mk (zeroSumIdeal)) ∘ baseInclude` vanishes on
`monomialInitialIdeal G`. -/
private lemma baseInclude_quot_vanishes_zero (a : MvPolynomial (BinomialEdgeVars (Fin n)) K)
    (ha : a ∈ monomialInitialIdeal (K := K) G) :
    (Ideal.Quotient.mk (zeroSumIdeal (K := K) G)).comp
      (baseInclude (K := K) n).toRingHom a = 0 := by
  have h := monomialInitialIdeal_le_baseInclude_comap_zeroSum (K := K) G ha
  rw [Ideal.mem_comap] at h
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact h

/-- Forward map: induced by `baseInclude` through the `S / monomialInitialIdeal`
quotient. -/
def specZeroQuotForward :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G →+*
    DefRing n K ⧸ zeroSumIdeal (K := K) G :=
  Ideal.Quotient.lift (monomialInitialIdeal (K := K) G)
    ((Ideal.Quotient.mk (zeroSumIdeal (K := K) G)).comp (baseInclude (K := K) n).toRingHom)
    (baseInclude_quot_vanishes_zero G)

/-- The composition `(mk monomialInitialIdeal) ∘ specZero` vanishes on
`tildeJ G ⊔ span{tDef n}`. -/
private lemma specZero_quot_vanishes_zero (a : DefRing n K)
    (ha : a ∈ zeroSumIdeal (K := K) G) :
    (Ideal.Quotient.mk (monomialInitialIdeal (K := K) G)).comp
      (specZero (K := K) n).toRingHom a = 0 := by
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [Submodule.mem_sup] at ha
  obtain ⟨i, hi, j, hj, rfl⟩ := ha
  rw [map_add]
  refine Ideal.add_mem _ ?_ ?_
  · have hmap : (specZero (K := K) n).toRingHom i ∈
        Ideal.map (specZero (K := K) n).toRingHom (tildeJ G) :=
      Ideal.mem_map_of_mem _ hi
    rw [tildeJ_specZero_eq] at hmap
    exact hmap
  · -- specZero(q * tDef) = specZero(q) * 0 = 0
    rw [Ideal.mem_span_singleton] at hj
    obtain ⟨q, rfl⟩ := hj
    have heq : (specZero (K := K) n).toRingHom (tDef n * q) = 0 := by
      rw [map_mul]
      change (specZero n) (X (Sum.inr ())) * (specZero n) q = 0
      rw [specZero_X_inr, zero_mul]
    rw [heq]
    exact Ideal.zero_mem _

/-- Backward map: induced by `specZero` through the
`DefRing / zeroSumIdeal` quotient. -/
def specZeroQuotBackward :
    DefRing n K ⧸ zeroSumIdeal (K := K) G →+*
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G :=
  Ideal.Quotient.lift (zeroSumIdeal (K := K) G)
    ((Ideal.Quotient.mk (monomialInitialIdeal (K := K) G)).comp
      (specZero (K := K) n).toRingHom)
    (specZero_quot_vanishes_zero G)

/-- `specZero ∘ baseInclude = identity` on `S`. -/
private lemma specZero_baseInclude (p : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    (specZero (K := K) n) ((baseInclude (K := K) n) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    change (specZero n) ((baseInclude n) (C r)) = C r
    rw [show (baseInclude (K := K) n) (C r) = C r from by simp [baseInclude],
        show (specZero (K := K) n) (C r) = C r from by simp [specZero]]
  | add p q hp hq =>
    change (specZero n) ((baseInclude n) (p + q)) = p + q
    rw [map_add, map_add, hp, hq]
  | mul_X p v ih =>
    change (specZero n) ((baseInclude n) (p * X v)) = p * X v
    rw [map_mul, map_mul, ih]
    have h1 : (baseInclude (K := K) n) (X v) = X (Sum.inl v) := by
      simp [baseInclude]
    rw [h1, specZero_X_inl]

/-- Modulo `zeroSumIdeal`, every variable equals its image under
`baseInclude ∘ specZero`. The only nontrivial case is `X (Sum.inr ()) = tDef n`,
which is directly in `span{tDef n}`. -/
private lemma quot_baseInclude_specZero_X (v : DefVars n) :
    (Ideal.Quotient.mk (zeroSumIdeal (K := K) G))
      ((baseInclude (K := K) n) ((specZero (K := K) n) (X v))) =
    (Ideal.Quotient.mk (zeroSumIdeal (K := K) G)) (X v) := by
  rcases v with v | u
  · rw [specZero_X_inl]
    have h1 : (baseInclude (K := K) n) (X v) = X (Sum.inl v) := by simp [baseInclude]
    rw [h1]
  · have hu : u = () := by cases u; rfl
    subst hu
    rw [specZero_X_inr, map_zero, Ideal.Quotient.eq]
    change (0 : DefRing n K) - tDef n ∈ zeroSumIdeal G
    rw [zero_sub]
    apply (Ideal.neg_mem_iff _).mpr
    apply Ideal.mem_sup_right
    exact Ideal.subset_span (Set.mem_singleton _)

/-- Backward composed with forward equals identity. -/
private lemma specZeroQuotBackward_specZeroQuotForward :
    (specZeroQuotBackward (K := K) G).comp (specZeroQuotForward (K := K) G) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (Ideal.Quotient.mk (monomialInitialIdeal G))
      ((specZero n) ((baseInclude n) p)) =
      (Ideal.Quotient.mk (monomialInitialIdeal G)) p
  rw [specZero_baseInclude]

/-- Forward composed with backward equals identity. -/
private lemma specZeroQuotForward_specZeroQuotBackward :
    (specZeroQuotForward (K := K) G).comp (specZeroQuotBackward (K := K) G) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (Ideal.Quotient.mk (zeroSumIdeal G))
      ((baseInclude n) ((specZero n) p)) =
      (Ideal.Quotient.mk (zeroSumIdeal G)) p
  induction p using MvPolynomial.induction_on with
  | C r =>
    have h1 : (specZero (K := K) n) (C r) = C r := by simp [specZero]
    have h2 : (baseInclude (K := K) n) (C r) = C r := by simp [baseInclude]
    rw [h1, h2]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p v ih =>
    rw [map_mul, map_mul, map_mul, ih, quot_baseInclude_specZero_X, ← map_mul]

/-- The ring iso `S ⧸ monomialInitialIdeal G ≃+* DefRing ⧸ (Ĩ ⊔ span{t})`
induced by the splitting `specZero ∘ baseInclude = id`. -/
def specZeroQuotEquiv :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G ≃+*
    DefRing n K ⧸ zeroSumIdeal (K := K) G :=
  RingEquiv.ofRingHom
    (specZeroQuotForward (K := K) G) (specZeroQuotBackward (K := K) G)
    (specZeroQuotForward_specZeroQuotBackward (K := K) G)
    (specZeroQuotBackward_specZeroQuotForward (K := K) G)

end SpecZeroQuotEquiv

/-! ## `K[t]`-algebra structure on the deformation ring

The deformation parameter ring is `K[t] ≃ MvPolynomial Unit K`, and the
inclusion `K[t] → S[t]` is `rename Sum.inr`. We register the corresponding
`Algebra` and `IsScalarTower` instances so that the deformation ring and its
quotient by `Ĩ` become `K[t]`-modules, which is the setting in which flatness
and the induced `IsSMulRegular` of `t - 1` are most cleanly stated. -/

/-- The deformation parameter ring `K[t]` realized as `MvPolynomial Unit K`. -/
abbrev PolyT (K : Type) [Field K] : Type := MvPolynomial Unit K

/-- The inclusion `K[t] ↪ S[t]` as a `K`-algebra homomorphism, sending the
    unique variable of `K[t]` to `tDef n = X (Sum.inr ())`. -/
def polyTInclude (n : ℕ) : PolyT K →ₐ[K] DefRing n K :=
  rename (Sum.inr : Unit → DefVars n)

@[simp] lemma polyTInclude_X (n : ℕ) (u : Unit) :
    polyTInclude (K := K) n (X u) = X (Sum.inr u) := by
  change rename _ _ = _
  rw [rename_X]

/-- `S[t] = DefRing n K` as a `K[t]`-algebra via `polyTInclude`. -/
noncomputable instance polyTAlgebra (n : ℕ) : Algebra (PolyT K) (DefRing n K) :=
  (polyTInclude (K := K) n).toAlgebra

/-- Scalar-tower compatibility `K → K[t] → S[t]`. -/
instance polyT_isScalarTower (n : ℕ) :
    IsScalarTower K (PolyT K) (DefRing n K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap K (DefRing n K) r =
    polyTInclude (K := K) n (algebraMap K (PolyT K) r)
  simp [polyTInclude]

/-- `PolyT K = MvPolynomial Unit K` is a PID, via transport from `Polynomial K`
    along `MvPolynomial.pUnitAlgEquiv`. In particular, it is a Bezout domain
    and a Dedekind domain, so the Mathlib "torsion-free ↔ flat" characterization
    applies to modules over `PolyT K`. -/
noncomputable instance : IsPrincipalIdealRing (PolyT K) :=
  let e : PolyT K ≃+* Polynomial K := (MvPolynomial.pUnitAlgEquiv K).toRingEquiv
  IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

/-! ## Monomial order on the deformation variable type

Infrastructure for the eventual Gröbner-basis proof of the colon-ideal
sub-sorry. We extend the paper's variable order `x_1 > x_2 > ... > y_1 > ...`
by placing the deformation parameter `t` at the bottom, then take the lex
monomial order. Under this order, every deformed generator `f̃_{i,j}` has
leading monomial `x_i y_j` (with no `t` factor), which is the structural
property needed for the Gröbner division algorithm over `K[t]`. -/

/-- The `DefVars n` type is finite. -/
instance defVars_Finite (n : ℕ) :
    Finite (DefVars n) :=
  inferInstanceAs (Finite (BinomialEdgeVars (Fin n) ⊕ Unit))

/-- Linear order on the deformation variable type `DefVars n`:
    the paper's `x > y` order on `BinomialEdgeVars (Fin n)` with `t = inr ()`
    strictly ABOVE every `x` and `y` (i.e. `t` is LARGEST under `defLE`, hence
    LEAST significant under the lex monomial order). This ensures the leading
    monomial of `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i` is `x_i y_j`. -/
@[reducible] def defLE {n : ℕ} (a b : DefVars n) : Prop :=
  match a, b with
  | Sum.inl u, Sum.inl v => (u : BinomialEdgeVars (Fin n)) ≤ v
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False

instance defVars_LinearOrder (n : ℕ) :
    LinearOrder (DefVars n) where
  le := defLE
  lt := fun a b => defLE a b ∧ ¬defLE b a
  toDecidableLE := Classical.decRel defLE
  le_refl a := by
    cases a
    · exact le_refl _
    · exact trivial
  le_trans a b c h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all only [defLE]
    exact le_trans h1 h2
  le_antisymm a b h1 h2 := by
    change (show DefVars n from a) = b
    cases a with
    | inl u =>
      cases b with
      | inl v =>
        simp only [defLE] at h1 h2
        exact congrArg Sum.inl (le_antisymm h1 h2)
      | inr _ => exact absurd h2 id
    | inr _ =>
      cases b with
      | inl _ => exact absurd h1 id
      | inr _ => rfl
  le_total a b := by
    cases a <;> cases b <;> simp only [defLE]
    · exact le_total _ _
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact Or.inl trivial

instance defVars_WellFoundedGT (n : ℕ) :
    @WellFoundedGT (DefVars n) (defVars_LinearOrder n).toLT :=
  @Finite.to_wellFoundedGT _ (defVars_Finite n) (defVars_LinearOrder n).toPreorder

/-- The lex monomial order on the deformation variable type. Under this order,
    the leading monomial of `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i` is
    `x_i y_j` (for `i < j`), with leading coefficient `1`. -/
noncomputable def deformationMonomialOrder (n : ℕ) :
    MonomialOrder (DefVars n) :=
  @MonomialOrder.lex (DefVars n)
    (defVars_LinearOrder n) (defVars_WellFoundedGT n)

/-! ### Leading term of `f̃_{i,j}`

The following two lemmas identify the leading monomial of each deformed
generator `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i` as `x_i y_j` (with leading
coefficient `1`). These are the structural inputs to the Gröbner-basis
argument for `tildeJ_polyT_colon_eq`. The proof pattern mirrors
`fij_leadingCoeff` / `fij_degree` in `BEI/MonomialOrder.lean`.

**Status (partial)**: The orientation of `defLE` is correctly arranged so
that `t = Sum.inr ()` is LARGEST in the defLE order (making it LEAST
significant in `MonomialOrder.lex`, per the convention
`toLex (single 0 2) > toLex (single 0 1 + single 1 1)` in
`Mathlib.Data.Finsupp.MonomialOrder`, where the smallest-in-α variable
is most significant). The three lemmas below are stated but carry a
`sorry`; their proofs require careful universe alignment for
`Sum.inl_injective` / `Sum.inr_ne_inl` on `DefVars n` and are deferred. -/

/-- Key lex inequality: under `deformationMonomialOrder`, the support of
    `t^(j-i) x_j y_i` is strictly less than the support of `x_i y_j`. The
    splitting index is `inl (inr j)` (= `y_j`) — the smallest variable (in
    `defLE`) at which the two supports differ. -/
private lemma fijTilde_lex_lt {n : ℕ} (i j : Fin n) (hij : i < j) :
    (deformationMonomialOrder n).toSyn
      ((Finsupp.single (Sum.inr ()) (j.val - i.val) +
         Finsupp.single (Sum.inl (Sum.inl j)) 1 +
         Finsupp.single (Sum.inl (Sum.inr i)) 1 :
          DefVars n →₀ ℕ)) <
    (deformationMonomialOrder n).toSyn
      ((Finsupp.single (Sum.inl (Sum.inl i)) 1 +
         Finsupp.single (Sum.inl (Sum.inr j)) 1 :
          DefVars n →₀ ℕ)) := by
  rw [Finsupp.Lex.lt_iff]
  refine ⟨(Sum.inl (Sum.inr j) : DefVars n), fun l hl => ?_, ?_⟩
  · -- For all l < Sum.inl (Sum.inr j) in defLE, both supports agree at l.
    obtain ⟨hle, hnle⟩ := hl
    rcases l with (v | u)
    · rcases v with (u | u)
      · -- l = Sum.inl (Sum.inl u): hle unfolds to binomialEdgeLE (inl u) (inr j) = False.
        exact absurd hle (by
          change ¬ binomialEdgeLE (Sum.inl u) (Sum.inr j)
          simp [binomialEdgeLE])
      · -- l = Sum.inl (Sum.inr u): need u > j; show all positions contribute 0.
        have hle' : binomialEdgeLE (Sum.inr u) (Sum.inr j) := hle
        have hnle' : ¬ binomialEdgeLE (Sum.inr j) (Sum.inr u) := hnle
        simp only [binomialEdgeLE] at hle' hnle'
        have huj : j.val < u.val := by
          have : j.val ≤ u.val := hle'
          omega
        have hne_ru : u ≠ j := by intro h; rw [h] at huj; exact lt_irrefl _ huj
        have hne_iu : u ≠ i := by
          intro h; rw [h] at huj; exact lt_irrefl _ (lt_trans hij huj)
        simp only [deformationMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk,
          ofLex_toLex, Finsupp.add_apply, Finsupp.single_apply]
        -- All positions at `inl (inr u)` (for u > j > i) evaluate to 0.
        have e1 : ((Sum.inr () : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have e2 : ((Sum.inl (Sum.inl j) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have e3 : ((Sum.inl (Sum.inr i) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          ⟨fun h => hne_iu.symm (by injections), fun h => h.elim⟩
        have e4 : ((Sum.inl (Sum.inl i) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have e5 : ((Sum.inl (Sum.inr j) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          ⟨fun h => hne_ru.symm (by injections), fun h => h.elim⟩
        simp [e1, e2, e3, e4, e5]
    · -- l = Sum.inr u: hle says defLE (inr u) (inl (inr j)) = False under flipped defLE.
      exact absurd hle (by change ¬ False; exact fun h => h)
  · -- At inl (inr j): LHS terms all evaluate to 0; RHS has 1 at inl (inr j).
    simp only [deformationMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk,
      ofLex_toLex, Finsupp.add_apply, Finsupp.single_apply]
    have e1 : ((Sum.inr () : DefVars n) = Sum.inl (Sum.inr j)) ↔ False :=
      by simp
    have e2 : ((Sum.inl (Sum.inl j) : DefVars n) = Sum.inl (Sum.inr j)) ↔ False :=
      by simp
    have e3 : ((Sum.inl (Sum.inr i) : DefVars n) = Sum.inl (Sum.inr j)) ↔ False :=
      ⟨fun h => (ne_of_lt hij) (by injections), fun h => h.elim⟩
    have e4 : ((Sum.inl (Sum.inl i) : DefVars n) = Sum.inl (Sum.inr j)) ↔ False :=
      by simp
    simp [e1, e2, e3, e4]

/-- The leading monomial of `f̃_{i,j}` (with `i < j`) under
    `deformationMonomialOrder` is `x_i y_j`: no `t` factor. -/
theorem degree_fijTilde {n : ℕ} {i j : Fin n} (hij : i < j) :
    (deformationMonomialOrder n).degree (fijTilde (K := K) i j) =
      (Finsupp.single (Sum.inl (Sum.inl i)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j)) 1 :
          DefVars n →₀ ℕ) := by
  set xi : DefRing n K := X (Sum.inl (Sum.inl i) : DefVars n) with hxi_def
  set yj : DefRing n K := X (Sum.inl (Sum.inr j) : DefVars n) with hyj_def
  set xj : DefRing n K := X (Sum.inl (Sum.inl j) : DefVars n) with hxj_def
  set yi : DefRing n K := X (Sum.inl (Sum.inr i) : DefVars n) with hyi_def
  set t  : DefRing n K := X (Sum.inr () : DefVars n) with ht_def
  change (deformationMonomialOrder n).degree
    (xi * yj - t ^ (j.val - i.val) * xj * yi) = _
  have hxi : xi ≠ 0 := X_ne_zero _
  have hyj : yj ≠ 0 := X_ne_zero _
  have hxj : xj ≠ 0 := X_ne_zero _
  have hyi : yi ≠ 0 := X_ne_zero _
  have ht : t ≠ 0 := X_ne_zero _
  have htpow : t ^ (j.val - i.val) ≠ 0 := pow_ne_zero _ ht
  have htpow_xj : t ^ (j.val - i.val) * xj ≠ 0 := mul_ne_zero htpow hxj
  have hdeg1 : (deformationMonomialOrder n).degree (xi * yj) =
      Finsupp.single (Sum.inl (Sum.inl i)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j)) 1 := by
    rw [MonomialOrder.degree_mul hxi hyj]
    change (deformationMonomialOrder n).degree (X _ : DefRing n K) +
        (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
  have hdegT : (deformationMonomialOrder n).degree (t ^ (j.val - i.val)) =
      Finsupp.single (Sum.inr ()) (j.val - i.val) := by
    rw [MonomialOrder.degree_pow]
    change (j.val - i.val) • (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hdeg2 : (deformationMonomialOrder n).degree
      (t ^ (j.val - i.val) * xj * yi) =
      Finsupp.single (Sum.inr ()) (j.val - i.val) +
        Finsupp.single (Sum.inl (Sum.inl j)) 1 +
        Finsupp.single (Sum.inl (Sum.inr i)) 1 := by
    rw [MonomialOrder.degree_mul htpow_xj hyi,
      MonomialOrder.degree_mul htpow hxj, hdegT]
    change _ + (deformationMonomialOrder n).degree (X _ : DefRing n K) +
        (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
  have hlt : (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree (t ^ (j.val - i.val) * xj * yi)) <
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (xi * yj)) := by
    rw [hdeg1, hdeg2]; exact fijTilde_lex_lt i j hij
  rw [MonomialOrder.degree_sub_of_lt hlt, hdeg1]

/-- The leading coefficient of `f̃_{i,j}` (with `i < j`) is `1`. -/
theorem leadingCoeff_fijTilde {n : ℕ} {i j : Fin n} (hij : i < j) :
    (deformationMonomialOrder n).leadingCoeff (fijTilde (K := K) i j) = 1 := by
  set xi : DefRing n K := X (Sum.inl (Sum.inl i) : DefVars n) with hxi_def
  set yj : DefRing n K := X (Sum.inl (Sum.inr j) : DefVars n) with hyj_def
  set xj : DefRing n K := X (Sum.inl (Sum.inl j) : DefVars n) with hxj_def
  set yi : DefRing n K := X (Sum.inl (Sum.inr i) : DefVars n) with hyi_def
  set t  : DefRing n K := X (Sum.inr () : DefVars n) with ht_def
  change (deformationMonomialOrder n).leadingCoeff
    (xi * yj - t ^ (j.val - i.val) * xj * yi) = _
  have hxi : xi ≠ 0 := X_ne_zero _
  have hyj : yj ≠ 0 := X_ne_zero _
  have hxj : xj ≠ 0 := X_ne_zero _
  have hyi : yi ≠ 0 := X_ne_zero _
  have ht : t ≠ 0 := X_ne_zero _
  have htpow : t ^ (j.val - i.val) ≠ 0 := pow_ne_zero _ ht
  have htpow_xj : t ^ (j.val - i.val) * xj ≠ 0 := mul_ne_zero htpow hxj
  have hdeg1 : (deformationMonomialOrder n).degree (xi * yj) =
      Finsupp.single (Sum.inl (Sum.inl i)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j)) 1 := by
    rw [MonomialOrder.degree_mul hxi hyj]
    change (deformationMonomialOrder n).degree (X _ : DefRing n K) +
        (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
  have hdegT : (deformationMonomialOrder n).degree (t ^ (j.val - i.val)) =
      Finsupp.single (Sum.inr ()) (j.val - i.val) := by
    rw [MonomialOrder.degree_pow]
    change (j.val - i.val) • (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hdeg2 : (deformationMonomialOrder n).degree
      (t ^ (j.val - i.val) * xj * yi) =
      Finsupp.single (Sum.inr ()) (j.val - i.val) +
        Finsupp.single (Sum.inl (Sum.inl j)) 1 +
        Finsupp.single (Sum.inl (Sum.inr i)) 1 := by
    rw [MonomialOrder.degree_mul htpow_xj hyi,
      MonomialOrder.degree_mul htpow hxj, hdegT]
    change _ + (deformationMonomialOrder n).degree (X _ : DefRing n K) +
        (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
  have hlt : (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree (t ^ (j.val - i.val) * xj * yi)) <
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (xi * yj)) := by
    rw [hdeg1, hdeg2]; exact fijTilde_lex_lt i j hij
  rw [MonomialOrder.leadingCoeff_sub_of_lt hlt, hxi_def, hyj_def,
    MonomialOrder.leadingCoeff_mul, MonomialOrder.leadingCoeff_X,
    MonomialOrder.leadingCoeff_X, mul_one]

/-- The image of `t - 1 ∈ K[t]` under the `K[t]`-algebra map into `S[t] ⧸ Ĩ`
    is the class of `tDef n - 1`. -/
lemma algebraMap_polyT_tMinusOne {n : ℕ} (G : SimpleGraph (Fin n)) :
    algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) (X () - 1) =
      Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1) := by
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  change (Ideal.Quotient.mk (tildeJ G))
      (polyTInclude (K := K) n (X () - 1)) = _
  simp [polyTInclude, tDef]

/-- The image of `t ∈ K[t]` under the `K[t]`-algebra map into `S[t] ⧸ Ĩ`
    is the class of `tDef n`. -/
lemma algebraMap_polyT_t {n : ℕ} (G : SimpleGraph (Fin n)) :
    algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) (X ()) =
      Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n) := by
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  change (Ideal.Quotient.mk (tildeJ G))
      (polyTInclude (K := K) n (X ())) = _
  simp [polyTInclude, tDef]

/-! ### Weight vector and weighted-homogeneity of `f̃_{i,j}` -/

/-- Weight function on `DefVars n` used for the Gröbner-deformation grading:

* `w(x_i) = 2 (n + 1 - i)` for `i : Fin n`,
* `w(y_j) = n + 1 - j` for `j : Fin n`,
* `w(t) = 1`.

Under this weight, each deformed generator
`f̃_{i,j} = x_i y_j - t^(j-i) · x_j y_i` is weighted-homogeneous of degree
`2(n+1-i) + (n+1-j) = (j-i) + 2(n+1-j) + (n+1-i)`, because the `t^(j-i)`
exponent is exactly the weight gap between the two monomials. -/
def defWeight (n : ℕ) : DefVars n → ℕ
  | Sum.inl (Sum.inl i) => 2 * (n + 1 - i.val)
  | Sum.inl (Sum.inr j) => n + 1 - j.val
  | Sum.inr _           => 1

@[simp] lemma defWeight_xi (n : ℕ) (i : Fin n) :
    defWeight n (Sum.inl (Sum.inl i) : DefVars n) = 2 * (n + 1 - i.val) := rfl

@[simp] lemma defWeight_yj (n : ℕ) (j : Fin n) :
    defWeight n (Sum.inl (Sum.inr j) : DefVars n) = n + 1 - j.val := rfl

@[simp] lemma defWeight_t (n : ℕ) :
    defWeight n (Sum.inr () : DefVars n) = 1 := rfl

/-- Every variable of `DefVars n` has strictly positive weight under
`defWeight n`. This is what makes the induced grading on `DefRing n K`
"connected" (degree-0 piece consists only of the constants). -/
lemma defWeight_pos {n : ℕ} (v : DefVars n) : 0 < defWeight n v := by
  rcases v with (a | b)
  · rcases a with (i | j)
    · change 0 < 2 * (n + 1 - i.val)
      have := i.isLt
      omega
    · change 0 < n + 1 - j.val
      have := j.isLt
      omega
  · exact Nat.zero_lt_one

/-- The common weight-homogeneous degree of the deformed generator
`f̃_{i,j} = x_i y_j - t^(j-i) · x_j y_i`. -/
def fijTildeDeg (n : ℕ) (i j : Fin n) : ℕ :=
  2 * (n + 1 - i.val) + (n + 1 - j.val)

/-- The deformed generator `f̃_{i,j}` (for `i < j`) is weighted-homogeneous of
degree `fijTildeDeg n i j = 2(n+1-i) + (n+1-j)` under `defWeight n`. Key
check: the two monomials `x_i y_j` and `t^(j-i) · x_j y_i` carry the same
total weight. -/
theorem isWeightedHomogeneous_fijTilde {n : ℕ} {i j : Fin n} (hij : i < j) :
    IsWeightedHomogeneous (defWeight n) (fijTilde (K := K) i j)
      (fijTildeDeg n i j) := by
  have hij_val : i.val < j.val := hij
  have hiN : i.val < n := i.isLt
  have hjN : j.val < n := j.isLt
  -- Name each variable as an element of `DefRing n K` to fix the implicit
  -- ring argument of `X`.
  set xi : DefRing n K := X (Sum.inl (Sum.inl i) : DefVars n) with hxi_def
  set yj : DefRing n K := X (Sum.inl (Sum.inr j) : DefVars n) with hyj_def
  set xj : DefRing n K := X (Sum.inl (Sum.inl j) : DefVars n) with hxj_def
  set yi : DefRing n K := X (Sum.inl (Sum.inr i) : DefVars n) with hyi_def
  set t  : DefRing n K := X (Sum.inr () : DefVars n) with ht_def
  -- Rewrite the target using these names.
  change IsWeightedHomogeneous (defWeight n)
    (xi * yj - t ^ (j.val - i.val) * xj * yi) (fijTildeDeg n i j)
  -- Each variable is weighted-homogeneous of its weight.
  have hxi : IsWeightedHomogeneous (defWeight n) xi (2 * (n + 1 - i.val)) :=
    isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inl (Sum.inl i) : DefVars n)
  have hyj : IsWeightedHomogeneous (defWeight n) yj (n + 1 - j.val) :=
    isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inl (Sum.inr j) : DefVars n)
  have hxj : IsWeightedHomogeneous (defWeight n) xj (2 * (n + 1 - j.val)) :=
    isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inl (Sum.inl j) : DefVars n)
  have hyi : IsWeightedHomogeneous (defWeight n) yi (n + 1 - i.val) :=
    isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inl (Sum.inr i) : DefVars n)
  have ht  : IsWeightedHomogeneous (defWeight n) t 1 :=
    isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inr () : DefVars n)
  -- Part 1: `xi * yj` is weighted-homogeneous of degree `fijTildeDeg n i j`.
  have h1 : IsWeightedHomogeneous (defWeight n) (xi * yj) (fijTildeDeg n i j) := by
    have h := hxi.mul hyj
    simpa [fijTildeDeg] using h
  -- Part 2: `t^(j-i) * xj * yi` is weighted-homogeneous of degree
  -- `fijTildeDeg n i j`.
  have h2 : IsWeightedHomogeneous (defWeight n)
      (t ^ (j.val - i.val) * xj * yi) (fijTildeDeg n i j) := by
    have ht_pow : IsWeightedHomogeneous (defWeight n)
        (t ^ (j.val - i.val)) (j.val - i.val) := by
      have := ht.pow (j.val - i.val)
      simpa using this
    have h := (ht_pow.mul hxj).mul hyi
    have hdeg : (j.val - i.val) + 2 * (n + 1 - j.val) + (n + 1 - i.val) =
        fijTildeDeg n i j := by
      simp only [fijTildeDeg]; omega
    simpa [hdeg] using h
  -- Conclude: subtract h1 and h2 inside the WH submodule.
  exact (weightedHomogeneousSubmodule K (defWeight n) (fijTildeDeg n i j)).sub_mem h1 h2

/-! ### Graded algebra structure on `DefRing n K` and homogeneity of `tildeJ G` -/

/-- The weight-grading of `DefRing n K`: the `i`-th piece is the `K`-submodule of
weighted-homogeneous polynomials of degree `i` under `defWeight n`. -/
def defGrading (n : ℕ) : ℕ → Submodule K (DefRing n K) :=
  weightedHomogeneousSubmodule K (defWeight n)

/-- `DefRing n K` is a graded `K`-algebra under the weight grading `defWeight n`. -/
noncomputable instance defGrading_isGradedAlgebra (n : ℕ) :
    GradedAlgebra (defGrading (K := K) n) :=
  weightedGradedAlgebra K (defWeight n)

/-- Each deformed generator `f̃_{i,j}` (for `i < j`) is a homogeneous element of
`DefRing n K` under the weight grading. -/
lemma fijTilde_isHomogeneousElem {n : ℕ} {i j : Fin n} (hij : i < j) :
    SetLike.IsHomogeneousElem (defGrading (K := K) n) (fijTilde i j) :=
  ⟨fijTildeDeg n i j, isWeightedHomogeneous_fijTilde hij⟩

/-- The deformation ideal `tildeJ G` is homogeneous w.r.t. the weight grading on
`DefRing n K`, because it is spanned by weighted-homogeneous generators
`f̃_{i,j}`. -/
theorem tildeJ_isHomogeneous {n : ℕ} (G : SimpleGraph (Fin n)) :
    (tildeJ (K := K) G).IsHomogeneous (defGrading (K := K) n) := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, j, _, hij, rfl⟩
  exact fijTilde_isHomogeneousElem hij

/-! ### Graded-ring structure on the quotient `DefRing n K ⧸ tildeJ G` -/

/-- The quotient-grading of `DefRing n K ⧸ tildeJ G`: the `i`-th piece is the
image of `defGrading n i` under the quotient map `DefRing n K → DefRing n K ⧸ tildeJ G`. -/
def tildeJQuotGrading {n : ℕ} (G : SimpleGraph (Fin n)) :
    ℕ → Submodule K (DefRing n K ⧸ tildeJ (K := K) G) :=
  GradedQuotient.gradedQuotientPiece (defGrading (K := K) n) (tildeJ G)

/-- `DefRing n K ⧸ tildeJ G` is a ℕ-graded `K`-algebra via `tildeJQuotGrading G`. -/
noncomputable instance tildeJQuotient_GradedRing {n : ℕ} (G : SimpleGraph (Fin n)) :
    GradedRing (tildeJQuotGrading (K := K) G) :=
  GradedQuotient.gradedRing (defGrading (K := K) n) (tildeJ G) (tildeJ_isHomogeneous G)

/-! ### Connected grading -/

/-- The weight function `defWeight n` is non-torsion: no positive multiple of any
variable's weight is zero (because every weight is strictly positive in ℕ). -/
lemma defWeight_nonTorsionWeight (n : ℕ) : NonTorsionWeight (defWeight n) := by
  apply nonTorsionWeight_of
  intro v
  exact Nat.pos_iff_ne_zero.mp (defWeight_pos v)

/-- A weighted-homogeneous polynomial of degree 0 over `defWeight n` is a
constant, because every monomial of positive total weight is ruled out. -/
lemma eq_C_coeff_zero_of_isWeightedHomogeneous_zero
    {n : ℕ} {p : DefRing n K}
    (hp : IsWeightedHomogeneous (defWeight n) p 0) :
    p = C (p.coeff 0) := by
  -- Every non-zero coefficient is at degree 0 (the zero Finsupp).
  have h0 : ∀ d, p.coeff d ≠ 0 → d = 0 := by
    intro d hcoeff
    have hweight : Finsupp.weight (defWeight n) d = 0 := hp hcoeff
    have hallzero : ∀ x : DefVars n, d x = 0 :=
      (weightedDegree_eq_zero_iff (defWeight_nonTorsionWeight n)).mp hweight
    ext v; exact hallzero v
  -- Conclude by extensionality on coefficients.
  ext d
  rw [coeff_C]
  by_cases hd : d = 0
  · simp [hd]
  · have hzero : p.coeff d = 0 := by
      by_contra hne
      exact hd (h0 d hne)
    simp [hzero, Ne.symm hd]

/-- **Connected grading** on `DefRing n K ⧸ tildeJ G`: every element of
degree 0 in the weight grading is the image of a scalar from `K`. -/
theorem tildeJQuotGrading_connectedGraded
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    GradedIrrelevant.ConnectedGraded (tildeJQuotGrading (K := K) G) := by
  intro x hx
  -- Unfold: x is the image of some `p : DefRing n K` that is WH of degree 0.
  obtain ⟨p, hp, hx_eq⟩ :=
    (Submodule.mem_map).mp (show x ∈ (defGrading (K := K) n 0).map
      (Ideal.Quotient.mkₐ K (tildeJ (K := K) G)).toLinearMap from hx)
  -- `p = C (p.coeff 0)` by the WH-of-degree-0 lemma.
  have hp_wh : IsWeightedHomogeneous (defWeight n) p 0 := hp
  set k := p.coeff 0 with hk_def
  have hp_eq : p = C k := eq_C_coeff_zero_of_isWeightedHomogeneous_zero hp_wh
  refine ⟨k, ?_⟩
  -- Goal: `algebraMap K (DefRing/tildeJ) k = x`.
  rw [← hx_eq]
  -- RHS unfolds to `Ideal.Quotient.mk (tildeJ G) p`.
  change algebraMap K (DefRing n K ⧸ tildeJ (K := K) G) k =
    Ideal.Quotient.mk (tildeJ (K := K) G) p
  rw [hp_eq, ← Ideal.Quotient.mk_comp_algebraMap]
  rfl

/-! ### Proper-ness of `tildeJ G` and `DefRing n K ⧸ tildeJ G`

Every generator `f̃_{i,j}` of `tildeJ G` is weighted-homogeneous of strictly
positive degree, so `tildeJ G` is contained in the irrelevant ideal of
`DefRing n K` under the weight grading. In particular `1 ∉ tildeJ G`, so the
quotient ring is nontrivial. -/

lemma fijTildeDeg_pos {n : ℕ} {i j : Fin n} (_hij : i < j) : 0 < fijTildeDeg n i j := by
  have := i.isLt
  simp only [fijTildeDeg]
  omega

/-- The deformation ideal `tildeJ G` is contained in the irrelevant ideal of
`DefRing n K` under the weight grading. -/
lemma tildeJ_le_irrelevant {n : ℕ} (G : SimpleGraph (Fin n)) :
    tildeJ (K := K) G ≤
      (HomogeneousIdeal.irrelevant (defGrading (K := K) n)).toIdeal := by
  rw [tildeJ]
  apply Ideal.span_le.mpr
  rintro p ⟨i, j, _, hij, rfl⟩
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ (fijTildeDeg_pos hij)
    (isWeightedHomogeneous_fijTilde (K := K) hij)

/-- The deformation ideal `tildeJ G` is a proper ideal (i.e. `1 ∉ tildeJ G`).
Proved via `tildeJ G ⊆ irrelevant` and `irrelevant ≠ ⊤`. -/
theorem tildeJ_ne_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    tildeJ (K := K) G ≠ ⊤ := by
  intro h
  have h1 : (1 : DefRing n K) ∈ tildeJ (K := K) G := h ▸ Submodule.mem_top
  have h2 : (1 : DefRing n K) ∈
      (HomogeneousIdeal.irrelevant (defGrading (K := K) n)).toIdeal :=
    tildeJ_le_irrelevant G h1
  -- But `1 ∉ irrelevant` because the degree-0 projection of `1` is `1 ≠ 0`.
  have h3 : GradedRing.proj (defGrading (K := K) n) 0 (1 : DefRing n K) = 0 :=
    (HomogeneousIdeal.mem_irrelevant_iff _ _).mp h2
  have h4 : GradedRing.proj (defGrading (K := K) n) 0 (1 : DefRing n K) = 1 := by
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (defGrading (K := K) n)
        SetLike.GradedOne.one_mem]
  rw [h4] at h3
  exact one_ne_zero h3

/-- `DefRing n K ⧸ tildeJ G` is nontrivial. -/
instance tildeJ_quotient_nontrivial {n : ℕ} (G : SimpleGraph (Fin n)) :
    Nontrivial (DefRing n K ⧸ tildeJ (K := K) G) :=
  Ideal.Quotient.nontrivial_iff.mpr (tildeJ_ne_top G)

/-- `tDef n = X (Sum.inr ())` is weighted-homogeneous of degree `1` under
`defWeight n`. -/
lemma isWeightedHomogeneous_tDef (n : ℕ) :
    IsWeightedHomogeneous (defWeight n) (tDef (K := K) n) 1 := by
  change IsWeightedHomogeneous (defWeight n) (X (Sum.inr () : DefVars n) : DefRing n K) 1
  exact isWeightedHomogeneous_X (R := K) (defWeight n) (Sum.inr () : DefVars n)

/-- The class of `tDef n` in `DefRing n K ⧸ tildeJ G` lies in the irrelevant
ideal under the quotient-grading. -/
lemma tDefClass_mem_irrelevant {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal.Quotient.mk (tildeJ (K := K) G) (tDef n) ∈
    (HomogeneousIdeal.irrelevant (tildeJQuotGrading (K := K) G)).toIdeal := by
  refine HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one ?_
  change (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef n) : DefRing n K ⧸ tildeJ G) ∈
    (defGrading (K := K) n 1).map (Ideal.Quotient.mkₐ K (tildeJ G)).toLinearMap
  exact ⟨tDef n, isWeightedHomogeneous_tDef n, rfl⟩

/-! ### R1.d scaffolding: Gröbner division and the standard-form property -/

/-- The set of BEI deformed generators for `tildeJ G`: one `f̃_{i,j}` per edge
    `{i, j}` with `i < j`. -/
def tildeJGenerators {n : ℕ} (G : SimpleGraph (Fin n)) : Set (DefRing n K) :=
  { p | ∃ i j : Fin n, G.Adj i j ∧ i < j ∧ p = fijTilde i j }

lemma tildeJ_eq_span_generators {n : ℕ} (G : SimpleGraph (Fin n)) :
    tildeJ (K := K) G = Ideal.span (tildeJGenerators G) := rfl

lemma tildeJGenerators_leadingCoeff_isUnit {n : ℕ} (G : SimpleGraph (Fin n))
    (b : DefRing n K) (hb : b ∈ tildeJGenerators (K := K) G) :
    IsUnit ((deformationMonomialOrder n).leadingCoeff b) := by
  obtain ⟨i, j, _, hij, rfl⟩ := hb
  rw [leadingCoeff_fijTilde hij]
  exact isUnit_one

/-- Weakest form of the division algorithm: given any `c ∈ DefRing n K`,
    decompose it as `c = Σ g(b) · b + r` with `b` ranging over the generators
    of `Ĩ`, such that `r`'s support avoids divisibility by any
    `degree (fijTilde i j)` for an edge `{i, j}` with `i < j`. The Σ-part
    lies in `tildeJ G`. -/
theorem tildeJ_div {n : ℕ} (G : SimpleGraph (Fin n)) (c : DefRing n K) :
    ∃ (g : ↑(tildeJGenerators (K := K) G) →₀ DefRing n K) (r : DefRing n K),
      c = (Finsupp.linearCombination (DefRing n K)
          (Subtype.val : ↑(tildeJGenerators G) → DefRing n K)) g + r ∧
      (Finsupp.linearCombination (DefRing n K)
          (Subtype.val : ↑(tildeJGenerators G) → DefRing n K)) g ∈ tildeJ (K := K) G ∧
      ∀ α ∈ r.support, ∀ (i j : Fin n), G.Adj i j → i < j →
        ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α) := by
  obtain ⟨g, r, hdecomp, _hdeg, hrSupp⟩ :=
    MonomialOrder.div_set (m := deformationMonomialOrder n)
      (tildeJGenerators_leadingCoeff_isUnit G) c
  refine ⟨g, r, hdecomp, ?_, ?_⟩
  · -- The `g`-part is in the span of the generators.
    rw [tildeJ_eq_span_generators,
      Finsupp.linearCombination_apply (DefRing n K)
        (v := (Subtype.val : ↑(tildeJGenerators G) → DefRing n K))]
    -- Goal: g.sum (fun b a => a • b) ∈ Ideal.span (tildeJGenerators G)
    refine Ideal.sum_mem _ fun b _ => ?_
    change g b * (b : DefRing n K) ∈ Ideal.span (tildeJGenerators G)
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span b.2)
  · -- Support of `r` avoids leading-term divisibility.
    intro α hα i j hadj hij
    have hb : fijTilde (K := K) i j ∈ tildeJGenerators (K := K) G :=
      ⟨i, j, hadj, hij, rfl⟩
    exact hrSupp α hα _ hb

/-! ### Buchberger helpers for `deformationMonomialOrder` -/

/-- `x_i` as an element of `DefRing n K`. -/
private noncomputable def xD {n : ℕ} (i : Fin n) : DefRing n K :=
  X (Sum.inl (Sum.inl i) : DefVars n)

/-- `y_j` as an element of `DefRing n K`. -/
private noncomputable def yD {n : ℕ} (j : Fin n) : DefRing n K :=
  X (Sum.inl (Sum.inr j) : DefVars n)

/-- `t` as an element of `DefRing n K`. -/
private noncomputable def tD (n : ℕ) : DefRing n K :=
  X (Sum.inr () : DefVars n)

private lemma fijTilde_eq {n : ℕ} (i j : Fin n) :
    fijTilde (K := K) i j =
      xD i * yD j - (tD n) ^ (j.val - i.val) * xD j * yD i := by
  rfl

private lemma xD_ne_zero {n : ℕ} (i : Fin n) : (xD (K := K) i) ≠ 0 :=
  X_ne_zero _

private lemma yD_ne_zero {n : ℕ} (i : Fin n) : (yD (K := K) i) ≠ 0 :=
  X_ne_zero _

private lemma tD_ne_zero {n : ℕ} : (tD (K := K) n) ≠ 0 :=
  X_ne_zero _

private lemma degree_xD {n : ℕ} (i : Fin n) :
    (deformationMonomialOrder n).degree (xD (K := K) i) =
      (Finsupp.single (Sum.inl (Sum.inl i)) 1 : DefVars n →₀ ℕ) := by
  change (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
  rw [MonomialOrder.degree_X]

private lemma degree_yD {n : ℕ} (i : Fin n) :
    (deformationMonomialOrder n).degree (yD (K := K) i) =
      (Finsupp.single (Sum.inl (Sum.inr i)) 1 : DefVars n →₀ ℕ) := by
  change (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
  rw [MonomialOrder.degree_X]

private lemma degree_tD (n : ℕ) :
    (deformationMonomialOrder n).degree (tD (K := K) n) =
      (Finsupp.single (Sum.inr ()) 1 : DefVars n →₀ ℕ) := by
  change (deformationMonomialOrder n).degree (X _ : DefRing n K) = _
  rw [MonomialOrder.degree_X]

private lemma degree_tD_pow {n : ℕ} (k : ℕ) :
    (deformationMonomialOrder n).degree ((tD (K := K) n) ^ k) =
      (Finsupp.single (Sum.inr ()) k : DefVars n →₀ ℕ) := by
  rw [MonomialOrder.degree_pow, degree_tD, Finsupp.smul_single, smul_eq_mul, mul_one]

private lemma zero_le_toSyn_def {n : ℕ} (d : DefVars n →₀ ℕ) :
    (deformationMonomialOrder n).toSyn 0 ≤ (deformationMonomialOrder n).toSyn d := by
  simp only [deformationMonomialOrder, MonomialOrder.lex, map_zero]
  exact bot_le

/-- If `f ∈ G`, then `q * f` has remainder `0` modulo `G` under
    `deformationMonomialOrder`. -/
private lemma isRemainder_single_mul_tilde {n : ℕ}
    (f q : DefRing n K) (G : Set (DefRing n K)) (h_mem : f ∈ G) :
    (deformationMonomialOrder n).IsRemainder (q * f) G 0 := by
  classical
  refine ⟨⟨Finsupp.single ⟨f, h_mem⟩ q, ?_, ?_⟩, ?_⟩
  · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
  · intro b
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · cases heq; rw [mul_comm]
    · simp only [mul_zero, MonomialOrder.degree_zero]
      exact zero_le_toSyn_def _
  · intro c hc; simp at hc

/-- `IsRemainder` for `q₁ · f₁ - q₂ · f₂` under `deformationMonomialOrder`,
    given the two-term degree bounds. -/
private lemma isRemainder_sub_mul_tilde {n : ℕ}
    (f₁ f₂ q₁ q₂ : DefRing n K) (G : Set (DefRing n K))
    (h₁ : f₁ ∈ G) (h₂ : f₂ ∈ G) (hne : f₁ ≠ f₂)
    (hdeg₁ : (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (q₁ * f₁)) ≤
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (q₁ * f₁ - q₂ * f₂)))
    (hdeg₂ : (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (q₂ * f₂)) ≤
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (q₁ * f₁ - q₂ * f₂))) :
    (deformationMonomialOrder n).IsRemainder (q₁ * f₁ - q₂ * f₂) G 0 := by
  classical
  constructor
  · set b₁ : G := ⟨f₁, h₁⟩
    set b₂ : G := ⟨f₂, h₂⟩
    have hb_ne : b₁ ≠ b₂ := fun h => hne (congr_arg Subtype.val h)
    refine ⟨Finsupp.single b₁ q₁ + Finsupp.single b₂ (-q₂), ?_, ?_⟩
    · simp only [map_add, Finsupp.linearCombination_single, smul_eq_mul, add_zero, b₁, b₂]
      ring
    · intro b
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      by_cases hb1 : b₁ = b
      · have hb2 : ¬(b₂ = b) := fun h => hb_ne (hb1.trans h.symm)
        simp only [if_pos hb1, if_neg hb2, add_zero]
        rw [show b.val = f₁ from congr_arg Subtype.val hb1.symm, mul_comm]
        exact hdeg₁
      · by_cases hb2 : b₂ = b
        · simp only [if_neg hb1, if_pos hb2, zero_add]
          rw [show b.val = f₂ from congr_arg Subtype.val hb2.symm,
            mul_neg, MonomialOrder.degree_neg, mul_comm]
          exact hdeg₂
        · simp only [if_neg hb1, if_neg hb2, add_zero, mul_zero,
            MonomialOrder.degree_zero]
          exact zero_le_toSyn_def _
  · intro c hc; simp at hc

/-- If `toSyn(deg f) ≠ toSyn(deg g)`, both degree bounds hold for `f - g`
    under `deformationMonomialOrder`. -/
private lemma degree_bounds_of_sub_tilde {n : ℕ}
    (f g : DefRing n K)
    (hne : (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree f) ≠
      (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree g)) :
    ((deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree f) ≤
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (f - g))) ∧
    ((deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree g) ≤
      (deformationMonomialOrder n).toSyn
        ((deformationMonomialOrder n).degree (f - g))) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hfg : f - g = -(g - f) := by ring
    rw [hfg, MonomialOrder.degree_neg, MonomialOrder.degree_sub_of_lt h]
    exact ⟨le_of_lt h, le_refl _⟩
  · rw [MonomialOrder.degree_sub_of_lt h]
    exact ⟨le_refl _, le_of_lt h⟩

/-! ### Tsub identities between degrees of deformed generators -/

private lemma fijTilde_ne_zero {n : ℕ} (i j : Fin n) (hij : i < j) :
    fijTilde (K := K) i j ≠ 0 := by
  intro h
  have := leadingCoeff_fijTilde (K := K) hij
  rw [h, MonomialOrder.leadingCoeff_zero] at this
  exact one_ne_zero this.symm

/-- Tsub identities for shared-first degrees:
    `d(f̃_{i,j₂}) - d(f̃_{i,j₁}) = single (inl (inr j₂)) 1` and symmetric. -/
private lemma degree_tsub_shared_first {n : ℕ} {i j₁ j₂ : Fin n}
    (hij₁ : i < j₁) (hij₂ : i < j₂) (hj : j₁ ≠ j₂) :
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i j₂) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i j₁) =
      (Finsupp.single (Sum.inl (Sum.inr j₂)) 1 : DefVars n →₀ ℕ)) ∧
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i j₁) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i j₂) =
      (Finsupp.single (Sum.inl (Sum.inr j₁)) 1 : DefVars n →₀ ℕ)) := by
  rw [degree_fijTilde hij₁, degree_fijTilde hij₂]
  refine ⟨?_, ?_⟩ <;> {
    ext v
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    rcases v with (v | u)
    · rcases v with (u | u)
      · -- v = Sum.inl (Sum.inl u)
        have h1 : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inl u)) ↔ False :=
          by simp
        have h2 : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inl u)) ↔ False :=
          by simp
        simp only [h1, h2, if_false, add_zero, Nat.sub_self]
      · -- v = Sum.inl (Sum.inr u)
        have hi : ((Sum.inl (Sum.inl i) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have hj1_eq : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inr u)) ↔ (j₁ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        have hj2_eq : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inr u)) ↔ (j₂ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        simp only [hi, hj1_eq, hj2_eq, if_false, zero_add]
        by_cases h1 : j₁ = u <;> by_cases h2 : j₂ = u
        · exact absurd (h1.trans h2.symm) hj
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
    · -- v = Sum.inr u
      have h1 : ((Sum.inl (Sum.inl i) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h2 : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h3 : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      simp only [h1, h2, h3, if_false, add_zero, Nat.sub_self]
  }

/-- Tsub identities for shared-last degrees. -/
private lemma degree_tsub_shared_last {n : ℕ} {i₁ i₂ j : Fin n}
    (hi₁j : i₁ < j) (hi₂j : i₂ < j) (hi : i₁ ≠ i₂) :
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i₂ j) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i₁ j) =
      (Finsupp.single (Sum.inl (Sum.inl i₂)) 1 : DefVars n →₀ ℕ)) ∧
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i₁ j) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i₂ j) =
      (Finsupp.single (Sum.inl (Sum.inl i₁)) 1 : DefVars n →₀ ℕ)) := by
  rw [degree_fijTilde hi₁j, degree_fijTilde hi₂j]
  refine ⟨?_, ?_⟩ <;> {
    ext v
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    rcases v with (v | u)
    · rcases v with (u | u)
      · -- v = Sum.inl (Sum.inl u)
        have hi1_eq : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inl (Sum.inl u)) ↔ (i₁ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        have hi2_eq : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inl u)) ↔ (i₂ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        simp only [hi1_eq, hi2_eq]
        by_cases h1 : i₁ = u <;> by_cases h2 : i₂ = u
        · exact absurd (h1.trans h2.symm) hi
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      · -- v = Sum.inl (Sum.inr u)
        have h1 : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have h2 : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        simp only [h1, h2, if_false, zero_add, Nat.sub_self]
    · -- v = Sum.inr u
      have h1 : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h2 : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h3 : ((Sum.inl (Sum.inr j) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      simp only [h1, h2, h3, if_false, add_zero, Nat.sub_self]
  }

/-- Tsub identities for coprime degrees. -/
private lemma degree_tsub_coprime {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi₁j₁ : i₁ < j₁) (hi₂j₂ : i₂ < j₂) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i₂ j₂) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i₁ j₁) =
      (Finsupp.single (Sum.inl (Sum.inl i₂)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j₂)) 1 : DefVars n →₀ ℕ)) ∧
    ((deformationMonomialOrder n).degree (fijTilde (K := K) i₁ j₁) -
        (deformationMonomialOrder n).degree (fijTilde (K := K) i₂ j₂) =
      (Finsupp.single (Sum.inl (Sum.inl i₁)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j₁)) 1 : DefVars n →₀ ℕ)) := by
  rw [degree_fijTilde hi₁j₁, degree_fijTilde hi₂j₂]
  refine ⟨?_, ?_⟩ <;> {
    ext v
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    rcases v with (v | u)
    · rcases v with (u | u)
      · -- v = Sum.inl (Sum.inl u)
        have h1 : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inl u)) ↔ False :=
          by simp
        have h2 : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inl u)) ↔ False :=
          by simp
        have hi1_eq : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inl (Sum.inl u)) ↔ (i₁ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        have hi2_eq : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inl u)) ↔ (i₂ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        simp only [h1, h2, hi1_eq, hi2_eq, if_false, add_zero]
        by_cases hu1 : i₁ = u <;> by_cases hu2 : i₂ = u
        · exact absurd (hu1.trans hu2.symm) hi
        · simp [hu1, hu2]
        · simp [hu1, hu2]
        · simp [hu1, hu2]
      · -- v = Sum.inl (Sum.inr u)
        have h1 : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have h2 : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inr u)) ↔ False :=
          by simp
        have hj1_eq : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inr u)) ↔ (j₁ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        have hj2_eq : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inr u)) ↔ (j₂ = u) :=
          ⟨fun h => by injections, fun h => by rw [h]⟩
        simp only [h1, h2, hj1_eq, hj2_eq, if_false, zero_add]
        by_cases hu1 : j₁ = u <;> by_cases hu2 : j₂ = u
        · exact absurd (hu1.trans hu2.symm) hj
        · simp [hu1, hu2]
        · simp [hu1, hu2]
        · simp [hu1, hu2]
    · -- v = Sum.inr u
      have h1 : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h2 : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h3 : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      have h4 : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inr u) ↔ False :=
        by simp
      simp only [h1, h2, h3, h4, if_false, add_zero, Nat.sub_self]
  }

/-! ### S-polynomial closed forms for `fijTilde` pairs -/

/-- S-polynomial of deformed generators sharing the first endpoint.
    Expressed as `y_{j₂} · f̃_{i,j₁} - y_{j₁} · f̃_{i,j₂}`, with the
    monomial factors unfolded to `X`. -/
private lemma sPolynomial_fijTilde_shared_first {n : ℕ}
    (i j₁ j₂ : Fin n) (hij₁ : i < j₁) (hij₂ : i < j₂) (hj : j₁ ≠ j₂) :
    (deformationMonomialOrder n).sPolynomial
        (fijTilde (K := K) i j₁) (fijTilde (K := K) i j₂) =
      yD j₂ * fijTilde (K := K) i j₁ -
        yD j₁ * fijTilde (K := K) i j₂ := by
  obtain ⟨htsub1, htsub2⟩ := degree_tsub_shared_first (K := K) hij₁ hij₂ hj
  rw [MonomialOrder.sPolynomial, htsub1, htsub2,
    leadingCoeff_fijTilde hij₁, leadingCoeff_fijTilde hij₂]
  rfl

/-- S-polynomial of deformed generators sharing the last endpoint. -/
private lemma sPolynomial_fijTilde_shared_last {n : ℕ}
    (i₁ i₂ j : Fin n) (hi₁j : i₁ < j) (hi₂j : i₂ < j) (hi : i₁ ≠ i₂) :
    (deformationMonomialOrder n).sPolynomial
        (fijTilde (K := K) i₁ j) (fijTilde (K := K) i₂ j) =
      xD i₂ * fijTilde (K := K) i₁ j -
        xD i₁ * fijTilde (K := K) i₂ j := by
  obtain ⟨htsub1, htsub2⟩ := degree_tsub_shared_last (K := K) hi₁j hi₂j hi
  rw [MonomialOrder.sPolynomial, htsub1, htsub2,
    leadingCoeff_fijTilde hi₁j, leadingCoeff_fijTilde hi₂j]
  rfl

private lemma monomial_sum_eq_X_mul_X {n : ℕ} (a b : DefVars n) :
    (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : K) :
      DefRing n K) = X a * X b := by
  rw [show (1 : K) = 1 * 1 from (mul_one 1).symm, ← monomial_mul]
  rfl

/-- S-polynomial of deformed generators with coprime leading monomials. -/
private lemma sPolynomial_fijTilde_coprime {n : ℕ}
    (i₁ i₂ j₁ j₂ : Fin n) (hi₁j₁ : i₁ < j₁) (hi₂j₂ : i₂ < j₂)
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    (deformationMonomialOrder n).sPolynomial
        (fijTilde (K := K) i₁ j₁) (fijTilde (K := K) i₂ j₂) =
      xD i₂ *
        yD j₂ * fijTilde (K := K) i₁ j₁ -
      xD i₁ *
        yD j₁ * fijTilde (K := K) i₂ j₂ := by
  obtain ⟨htsub1, htsub2⟩ := degree_tsub_coprime (K := K) hi₁j₁ hi₂j₂ hi hj
  rw [MonomialOrder.sPolynomial, htsub1, htsub2,
    leadingCoeff_fijTilde hi₁j₁, leadingCoeff_fijTilde hi₂j₂,
    monomial_sum_eq_X_mul_X (K := K), monomial_sum_eq_X_mul_X (K := K)]
  rfl

/-! ### Ring identities expressing S-polys as multiples of single generators -/

/-- For `i < j₁ < j₂`, the shared-first S-poly equals
    `-t^(j₁ - i) · y_i · f̃_{j₁, j₂}`. -/
private lemma sPolynomial_fijTilde_shared_first_lt {n : ℕ}
    (i j₁ j₂ : Fin n) (hij₁ : i < j₁) (hj₁j₂ : j₁ < j₂) :
    yD j₂ * fijTilde (K := K) i j₁ -
        yD j₁ * fijTilde (K := K) i j₂ =
    -(tD n ^ (j₁.val - i.val) *
      yD i) * fijTilde (K := K) j₁ j₂ := by
  have hsum : j₂.val - i.val = (j₁.val - i.val) + (j₂.val - j₁.val) := by
    have := Fin.lt_def.mp hij₁
    have := Fin.lt_def.mp hj₁j₂
    omega
  simp only [fijTilde, yD, tD]
  rw [hsum, pow_add]
  ring

/-- For `i < j₂ < j₁`, the shared-first S-poly equals
    `t^(j₂ - i) · y_i · f̃_{j₂, j₁}`. -/
private lemma sPolynomial_fijTilde_shared_first_gt {n : ℕ}
    (i j₁ j₂ : Fin n) (hij₂ : i < j₂) (hj₂j₁ : j₂ < j₁) :
    yD j₂ * fijTilde (K := K) i j₁ -
        yD j₁ * fijTilde (K := K) i j₂ =
    (tD n ^ (j₂.val - i.val) *
      yD i) * fijTilde (K := K) j₂ j₁ := by
  have hsum : j₁.val - i.val = (j₂.val - i.val) + (j₁.val - j₂.val) := by
    have := Fin.lt_def.mp hij₂
    have := Fin.lt_def.mp hj₂j₁
    omega
  simp only [fijTilde, yD, tD]
  rw [hsum, pow_add]
  ring

/-- For `i₁ < i₂ < j`, the shared-last S-poly equals
    `t^(j - i₂) · x_j · f̃_{i₁, i₂}`. -/
private lemma sPolynomial_fijTilde_shared_last_lt {n : ℕ}
    (i₁ i₂ j : Fin n) (hi₁i₂ : i₁ < i₂) (hi₂j : i₂ < j) :
    xD i₂ * fijTilde (K := K) i₁ j -
        xD i₁ * fijTilde (K := K) i₂ j =
    (tD n ^ (j.val - i₂.val) *
      xD j) * fijTilde (K := K) i₁ i₂ := by
  have hsum : j.val - i₁.val = (i₂.val - i₁.val) + (j.val - i₂.val) := by
    have := Fin.lt_def.mp hi₁i₂
    have := Fin.lt_def.mp hi₂j
    omega
  simp only [fijTilde, xD, tD]
  rw [hsum, pow_add]
  ring

/-- For `i₂ < i₁ < j`, the shared-last S-poly equals
    `-t^(j - i₁) · x_j · f̃_{i₂, i₁}`. -/
private lemma sPolynomial_fijTilde_shared_last_gt {n : ℕ}
    (i₁ i₂ j : Fin n) (hi₂i₁ : i₂ < i₁) (hi₁j : i₁ < j) :
    xD i₂ * fijTilde (K := K) i₁ j -
        xD i₁ * fijTilde (K := K) i₂ j =
    -(tD n ^ (j.val - i₁.val) *
      xD j) * fijTilde (K := K) i₂ i₁ := by
  have hsum : j.val - i₂.val = (i₁.val - i₂.val) + (j.val - i₁.val) := by
    have := Fin.lt_def.mp hi₂i₁
    have := Fin.lt_def.mp hi₁j
    omega
  simp only [fijTilde, xD, tD]
  rw [hsum, pow_add]
  ring

/-- Coprime-case ring identity. -/
private lemma sPolynomial_fijTilde_coprime_twist {n : ℕ}
    (i₁ i₂ j₁ j₂ : Fin n) (_hi₁j₁ : i₁ < j₁) (_hi₂j₂ : i₂ < j₂) :
    xD i₂ *
        yD j₂ * fijTilde (K := K) i₁ j₁ -
      xD i₁ *
        yD j₁ * fijTilde (K := K) i₂ j₂ =
    (tD n ^ (j₂.val - i₂.val) *
      xD j₂ *
        yD i₂) *
        fijTilde (K := K) i₁ j₁ -
    (tD n ^ (j₁.val - i₁.val) *
      xD j₁ *
        yD i₁) *
        fijTilde (K := K) i₂ j₂ := by
  simp only [fijTilde, xD, yD, tD]
  ring

/-! ### Degree distinctness in the coprime case -/

/-- The degrees of `t^(j₂-i₂)·x_{j₂}·y_{i₂}·f̃_{i₁,j₁}` and
    `t^(j₁-i₁)·x_{j₁}·y_{i₁}·f̃_{i₂,j₂}` differ (when `i₁ ≠ i₂`). -/
private lemma coprime_twisted_degrees_ne {n : ℕ}
    (i₁ i₂ j₁ j₂ : Fin n) (hi₁j₁ : i₁ < j₁) (hi₂j₂ : i₂ < j₂) (hi : i₁ ≠ i₂) :
    (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree
        ((tD n) ^ (j₂.val - i₂.val) *
          xD j₂ * yD i₂ *
          fijTilde (K := K) i₁ j₁)) ≠
    (deformationMonomialOrder n).toSyn
      ((deformationMonomialOrder n).degree
        ((tD n) ^ (j₁.val - i₁.val) *
          xD j₁ * yD i₁ *
          fijTilde (K := K) i₂ j₂)) := by
  have ht : (tD (K := K) n) ≠ 0 := tD_ne_zero
  have hxj₁ : (xD (K := K) j₁) ≠ 0 := xD_ne_zero _
  have hxj₂ : (xD (K := K) j₂) ≠ 0 := xD_ne_zero _
  have hyi₁ : (yD (K := K) i₁) ≠ 0 := yD_ne_zero _
  have hyi₂ : (yD (K := K) i₂) ≠ 0 := yD_ne_zero _
  have htpow1 : ((tD (K := K) n)) ^ (j₁.val - i₁.val) ≠ 0 := pow_ne_zero _ ht
  have htpow2 : ((tD (K := K) n)) ^ (j₂.val - i₂.val) ≠ 0 := pow_ne_zero _ ht
  have hfij1 : fijTilde (K := K) i₁ j₁ ≠ 0 := fijTilde_ne_zero (K := K) i₁ j₁ hi₁j₁
  have hfij2 : fijTilde (K := K) i₂ j₂ ≠ 0 := fijTilde_ne_zero (K := K) i₂ j₂ hi₂j₂
  have hdX1 : (deformationMonomialOrder n).degree
      (tD n ^ (j₂.val - i₂.val) *
        xD j₂ * yD i₂ *
        fijTilde (K := K) i₁ j₁) =
      (Finsupp.single (Sum.inr ()) (j₂.val - i₂.val) +
      Finsupp.single (Sum.inl (Sum.inl j₂)) 1 +
      Finsupp.single (Sum.inl (Sum.inr i₂)) 1 +
      (Finsupp.single (Sum.inl (Sum.inl i₁)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j₁)) 1) : DefVars n →₀ ℕ) := by
    rw [MonomialOrder.degree_mul (mul_ne_zero (mul_ne_zero htpow2 hxj₂) hyi₂) hfij1,
      MonomialOrder.degree_mul (mul_ne_zero htpow2 hxj₂) hyi₂,
      MonomialOrder.degree_mul htpow2 hxj₂,
      degree_tD_pow, degree_xD, degree_yD, degree_fijTilde hi₁j₁]
  have hdX2 : (deformationMonomialOrder n).degree
      (tD n ^ (j₁.val - i₁.val) *
        xD j₁ * yD i₁ *
        fijTilde (K := K) i₂ j₂) =
      (Finsupp.single (Sum.inr ()) (j₁.val - i₁.val) +
      Finsupp.single (Sum.inl (Sum.inl j₁)) 1 +
      Finsupp.single (Sum.inl (Sum.inr i₁)) 1 +
      (Finsupp.single (Sum.inl (Sum.inl i₂)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j₂)) 1) : DefVars n →₀ ℕ) := by
    rw [MonomialOrder.degree_mul (mul_ne_zero (mul_ne_zero htpow1 hxj₁) hyi₁) hfij2,
      MonomialOrder.degree_mul (mul_ne_zero htpow1 hxj₁) hyi₁,
      MonomialOrder.degree_mul htpow1 hxj₁,
      degree_tD_pow, degree_xD, degree_yD, degree_fijTilde hi₂j₂]
  rw [hdX1, hdX2]
  intro h
  have heq := (deformationMonomialOrder n).toSyn.injective h
  have h1 := Finsupp.ext_iff.mp heq (Sum.inl (Sum.inl i₁) : DefVars n)
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h1
  -- Evaluate both sides at (inl (inl i₁)):
  -- LHS: has 1 from f̃_{i₁,j₁} leading term, plus possible 1 if j₂ = i₁.
  -- RHS: has 1 iff j₁ = i₁ (false) or i₂ = i₁ (false).
  have hnei_j₁ : ((Sum.inl (Sum.inl j₁) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => hi₁j₁.ne' (Sum.inl.inj (Sum.inl.inj h)), fun h => h.elim⟩
  have hnei_i₂ : ((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => hi (Sum.inl.inj (Sum.inl.inj h)).symm, fun h => h.elim⟩
  have hnei_i₁_inr1 : ((Sum.inl (Sum.inr i₁) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => Sum.inr_ne_inl (Sum.inl.inj h), fun h => h.elim⟩
  have hnei_i₂_inr : ((Sum.inl (Sum.inr i₂) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => Sum.inr_ne_inl (Sum.inl.inj h), fun h => h.elim⟩
  have hnei_j₁_inr : ((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => Sum.inr_ne_inl (Sum.inl.inj h), fun h => h.elim⟩
  have hnei_j₂_inr : ((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨fun h => Sum.inr_ne_inl (Sum.inl.inj h), fun h => h.elim⟩
  have hnei_tX : ((Sum.inr () : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ False :=
    ⟨Sum.inr_ne_inl, fun h => h.elim⟩
  have hself_i₁ : ((Sum.inl (Sum.inl i₁) : DefVars n) = Sum.inl (Sum.inl i₁)) ↔ True :=
    ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [hnei_j₁, hnei_i₂, hnei_i₁_inr1, hnei_i₂_inr, hnei_j₁_inr, hnei_j₂_inr,
    hnei_tX, if_false, if_true, zero_add, add_zero] at h1
  omega

set_option maxHeartbeats 800000 in
-- The Buchberger S-polynomial case analysis (shared-first / shared-last /
-- coprime) unfolds to large polynomial identities; the default heartbeat
-- budget is insufficient for the elaborator to process all three cases.
/-- **R1.d Gröbner basis structure** (for closed graphs): `{f̃_{i,j}}` is
    a Gröbner basis of `Ĩ` for closed graphs — the deformed analogue of
    `closed_implies_groebner` in `BEI/ClosedGraphs.lean`. -/
theorem tildeJ_isGroebnerBasis {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) :
    (deformationMonomialOrder n).IsGroebnerBasis (tildeJGenerators (K := K) G)
      (tildeJ (K := K) G) := by
  classical
  rw [tildeJ_eq_span_generators,
    (deformationMonomialOrder n).isGroebnerBasis_iff_sPolynomial_isRemainder
      (tildeJGenerators_leadingCoeff_isUnit (K := K) G)]
  intro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
  obtain ⟨i₁, j₁, hadj₁, hij₁, hg₁_eq⟩ := hg₁
  obtain ⟨i₂, j₂, hadj₂, hij₂, hg₂_eq⟩ := hg₂
  have hg₁_fij : g₁ = fijTilde (K := K) i₁ j₁ := hg₁_eq
  have hg₂_fij : g₂ = fijTilde (K := K) i₂ j₂ := hg₂_eq
  simp only [hg₁_fij, hg₂_fij]
  by_cases heq_i : i₁ = i₂ <;> by_cases heq_j : j₁ = j₂
  · -- Same pair
    subst heq_i; subst heq_j
    rw [MonomialOrder.sPolynomial_self]
    exact ⟨⟨0, by simp, fun b => by
      simp [mul_zero, MonomialOrder.degree_zero]⟩,
      fun _ hc => by simp at hc⟩
  · -- Shared first (i₁ = i₂, j₁ ≠ j₂)
    subst heq_i
    rw [sPolynomial_fijTilde_shared_first i₁ j₁ j₂ hij₁ hij₂ heq_j]
    have hadj_jj : G.Adj j₁ j₂ := hClosed.1 hij₁ hij₂ heq_j hadj₁ hadj₂
    rcases lt_or_gt_of_ne heq_j with hjlt | hjgt
    · -- j₁ < j₂
      rw [sPolynomial_fijTilde_shared_first_lt (K := K) i₁ j₁ j₂ hij₁ hjlt]
      have hmem : fijTilde (K := K) j₁ j₂ ∈ tildeJGenerators (K := K) G :=
        ⟨j₁, j₂, hadj_jj, hjlt, rfl⟩
      exact isRemainder_single_mul_tilde (fijTilde j₁ j₂)
        (-((tD n) ^ (j₁.val - i₁.val) *
          yD i₁)) _ hmem
    · -- j₂ < j₁
      rw [sPolynomial_fijTilde_shared_first_gt (K := K) i₁ j₁ j₂ hij₂ hjgt]
      have hmem : fijTilde (K := K) j₂ j₁ ∈ tildeJGenerators (K := K) G :=
        ⟨j₂, j₁, hadj_jj.symm, hjgt, rfl⟩
      exact isRemainder_single_mul_tilde (fijTilde j₂ j₁)
        ((tD n) ^ (j₂.val - i₁.val) *
          yD i₁) _ hmem
  · -- Shared last (j₁ = j₂, i₁ ≠ i₂)
    subst heq_j
    rw [sPolynomial_fijTilde_shared_last i₁ i₂ j₁ hij₁ hij₂ heq_i]
    have hadj_ii : G.Adj i₁ i₂ := hClosed.2 hij₁ hij₂ heq_i hadj₁ hadj₂
    rcases lt_or_gt_of_ne heq_i with hilt | higt
    · -- i₁ < i₂
      rw [sPolynomial_fijTilde_shared_last_lt (K := K) i₁ i₂ j₁ hilt hij₂]
      have hmem : fijTilde (K := K) i₁ i₂ ∈ tildeJGenerators (K := K) G :=
        ⟨i₁, i₂, hadj_ii, hilt, rfl⟩
      exact isRemainder_single_mul_tilde (fijTilde i₁ i₂)
        ((tD n) ^ (j₁.val - i₂.val) *
          xD j₁) _ hmem
    · -- i₂ < i₁
      rw [sPolynomial_fijTilde_shared_last_gt (K := K) i₁ i₂ j₁ higt hij₁]
      have hmem : fijTilde (K := K) i₂ i₁ ∈ tildeJGenerators (K := K) G :=
        ⟨i₂, i₁, hadj_ii.symm, higt, rfl⟩
      exact isRemainder_single_mul_tilde (fijTilde i₂ i₁)
        (-((tD n) ^ (j₁.val - i₁.val) *
          xD j₁)) _ hmem
  · -- Coprime (i₁ ≠ i₂, j₁ ≠ j₂)
    rw [sPolynomial_fijTilde_coprime i₁ i₂ j₁ j₂ hij₁ hij₂ heq_i heq_j,
      sPolynomial_fijTilde_coprime_twist (K := K) i₁ i₂ j₁ j₂ hij₁ hij₂]
    have hfij_ne : fijTilde (K := K) i₁ j₁ ≠ fijTilde (K := K) i₂ j₂ := by
      intro heq
      have h1 := congr_arg (deformationMonomialOrder n).degree heq
      rw [degree_fijTilde hij₁, degree_fijTilde hij₂] at h1
      have h2 := Finsupp.ext_iff.mp h1 (Sum.inl (Sum.inl i₁) : DefVars n)
      simp only [Finsupp.add_apply, Finsupp.single_apply] at h2
      have hne_i2_i1 : ¬((Sum.inl (Sum.inl i₂) : DefVars n) = Sum.inl (Sum.inl i₁)) :=
        fun h => heq_i (Sum.inl.inj (Sum.inl.inj h)).symm
      have hne_j1 : ¬((Sum.inl (Sum.inr j₁) : DefVars n) = Sum.inl (Sum.inl i₁)) :=
        fun h => Sum.inr_ne_inl (Sum.inl.inj h)
      have hne_j2 : ¬((Sum.inl (Sum.inr j₂) : DefVars n) = Sum.inl (Sum.inl i₁)) :=
        fun h => Sum.inr_ne_inl (Sum.inl.inj h)
      rw [if_neg hne_j1, if_neg hne_i2_i1, if_neg hne_j2] at h2
      simp at h2
    have hmem₁ : fijTilde (K := K) i₁ j₁ ∈ tildeJGenerators (K := K) G :=
      ⟨i₁, j₁, hadj₁, hij₁, rfl⟩
    have hmem₂ : fijTilde (K := K) i₂ j₂ ∈ tildeJGenerators (K := K) G :=
      ⟨i₂, j₂, hadj₂, hij₂, rfl⟩
    have hne := coprime_twisted_degrees_ne (K := K) i₁ i₂ j₁ j₂ hij₁ hij₂ heq_i
    obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_sub_tilde
      ((tD n) ^ (j₂.val - i₂.val) *
        xD j₂ * yD i₂ *
        fijTilde (K := K) i₁ j₁)
      ((tD n) ^ (j₁.val - i₁.val) *
        xD j₁ * yD i₁ *
        fijTilde (K := K) i₂ j₂) hne
    exact isRemainder_sub_mul_tilde (fijTilde i₁ j₁) (fijTilde i₂ j₂)
      ((tD n) ^ (j₂.val - i₂.val) *
        xD j₂ * yD i₂)
      ((tD n) ^ (j₁.val - i₁.val) *
        xD j₁ * yD i₁)
      _ hmem₁ hmem₂ hfij_ne hd₁ hd₂

/-- **R1.d Gröbner basis property** (consequence of `tildeJ_isGroebnerBasis`):
    if `p ∈ Ĩ` has support avoiding `x_i y_j`-divisibility for every edge
    `{i, j}` with `i < j`, then `p = 0`.

    Proof: assume `p ≠ 0`. By `exists_degree_le_of_mem` applied to the
    Gröbner basis, some `f̃_{i,j}` has `degree(f̃_{i,j}) ≤ degree(p)`. By
    Step 2, `degree(f̃_{i,j}) = x_i y_j`. But `degree(p) ∈ p.support` (the
    leading-term position), and the hypothesis says this position is not
    `x_i y_j`-divisible. Contradiction. -/
theorem tildeJ_gbProperty {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (p : DefRing n K)
    (hp : p ∈ tildeJ (K := K) G)
    (hsupp : ∀ α ∈ p.support, ∀ (i j : Fin n), G.Adj i j → i < j →
      ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α)) :
    p = 0 := by
  by_contra hp0
  -- `{f̃_{i,j}}` is a Gröbner basis of `Ĩ` (by tildeJ_isGroebnerBasis).
  have hGB := tildeJ_isGroebnerBasis (K := K) (G := G) hClosed
  -- Extract some generator `b` with `degree(b) ≤ degree(p)`.
  obtain ⟨b, hb, _hb0, hdeg_le⟩ :=
    (deformationMonomialOrder n).exists_degree_le_of_mem hGB hp hp0
  -- `b` is some `fijTilde i j` with i<j, G.Adj i j.
  obtain ⟨i, j, hadj, hij, rfl⟩ := hb
  -- degree(p) is in p.support.
  have hdeg_supp : (deformationMonomialOrder n).degree p ∈ p.support :=
    (deformationMonomialOrder n).degree_mem_support hp0
  -- Apply the standard-support hypothesis at α = degree p.
  exact hsupp _ hdeg_supp i j hadj hij hdeg_le

/-- Support of `polyTInclude q * r` inherits the "avoids `x_i y_j`
    divisibility" property from `r`, because `polyTInclude q` only carries
    `t`-content, leaving the `x/y` part of each monomial unchanged. -/
lemma polyTInclude_mul_support_avoids {n : ℕ} {G : SimpleGraph (Fin n)}
    (q : PolyT K) (r : DefRing n K)
    (hrSupp : ∀ α ∈ r.support, ∀ (i j : Fin n), G.Adj i j → i < j →
      ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α)) :
    ∀ α ∈ (polyTInclude (K := K) n q * r).support,
      ∀ (i j : Fin n), G.Adj i j → i < j →
        ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α) := by
  intro α hα i j hadj hij
  -- α ∈ supp (polyTInclude q * r) ⊆ supp (polyTInclude q) + supp r (Minkowski sum)
  have hsub := MvPolynomial.support_mul (polyTInclude (K := K) n q) r hα
  rw [Finset.mem_add] at hsub
  obtain ⟨αq, hαq, β, hβ, hαq_β⟩ := hsub
  -- polyTInclude q = rename Sum.inr q, so αq is of the form Finsupp.mapDomain Sum.inr γ.
  have hαq_def : αq ∈ (MvPolynomial.rename (Sum.inr : Unit → DefVars n) q).support := hαq
  rw [MvPolynomial.support_rename_of_injective Sum.inr_injective] at hαq_def
  obtain ⟨γ, _hγ, hγ_eq⟩ := Finset.mem_image.mp hαq_def
  -- Key structural claim: for any `Sum.inl v`, αq(Sum.inl v) = 0.
  have hαq_inl_zero : ∀ v : BinomialEdgeVars (Fin n),
      αq (Sum.inl v : DefVars n) = 0 := by
    intro v
    rw [← hγ_eq]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    exact absurd hu (by intro h; injections)
  -- So α(Sum.inl v) = (αq + β)(Sum.inl v) = β(Sum.inl v).
  have hα_inl : ∀ v : BinomialEdgeVars (Fin n),
      α (Sum.inl v : DefVars n) = β (Sum.inl v : DefVars n) := by
    intro v
    rw [← hαq_β, Finsupp.add_apply, hαq_inl_zero, zero_add]
  -- Apply the r-support property to β: need to transfer `deg ≤ α → deg ≤ β`.
  intro hle_α
  apply hrSupp β hβ i j hadj hij
  -- Show deg(fijTilde i j) ≤ β; compare pointwise.
  rw [degree_fijTilde hij] at hle_α ⊢
  intro v
  have hαv :
      (Finsupp.single (Sum.inl (Sum.inl i)) 1 +
        Finsupp.single (Sum.inl (Sum.inr j)) 1 :
          DefVars n →₀ ℕ) v ≤ α v := hle_α v
  -- Case-split on v = Sum.inl _ vs Sum.inr _.
  rcases v with v | u
  · -- v = Sum.inl _: α and β agree there.
    rw [← hα_inl v]; exact hαv
  · -- v = Sum.inr u: deg is 0 at Sum.inr _, so trivially 0 ≤ β(v).
    simp

/-- **R1.d colon-ideal** (for closed graphs): for every nonzero polynomial
    `q ∈ K[t]`, the ideal `Ĩ` is saturated with respect to `polyTInclude q`.

    This is the BEI-specific content of `tildeJ_flat_over_polyT`: since
    `PolyT K = K[t]` is a PID, flatness of `DefRing n K ⧸ Ĩ` over `PolyT K`
    reduces to torsion-freeness, which in turn reduces to the statement below
    (via `Module.IsTorsionFree.mk` together with the fact that in a domain
    every regular element is nonzero).

    Assembly: use `tildeJ_div` to split `c = Σ g_b f̃_b + r` with standard `r`;
    then `polyTInclude q * r ∈ tildeJ G` has standard support, so
    `tildeJ_gbProperty` gives `polyTInclude q * r = 0`; `DefRing` is a domain
    and `polyTInclude q ≠ 0`, so `r = 0` and `c ∈ tildeJ G`. -/
theorem tildeJ_polyT_colon_eq
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G)
    (q : PolyT K) (hq : q ≠ 0)
    (c : DefRing n K) (hmul : polyTInclude (K := K) n q * c ∈ tildeJ (K := K) G) :
    c ∈ tildeJ (K := K) G := by
  obtain ⟨g, r, hdecomp, hgmem, hrSupp⟩ := tildeJ_div G c
  -- Split `polyTInclude q * c = polyTInclude q * (Σ g_b f̃_b) + polyTInclude q * r`.
  -- The first part is in `tildeJ G`; so is their sum (by hmul). Hence the
  -- second part is in `tildeJ G` as well.
  have hprod_mem : polyTInclude (K := K) n q * r ∈ tildeJ (K := K) G := by
    have h1 : polyTInclude (K := K) n q *
        (Finsupp.linearCombination (DefRing n K)
          (Subtype.val : ↑(tildeJGenerators G) → DefRing n K)) g ∈ tildeJ (K := K) G :=
      Ideal.mul_mem_left _ _ hgmem
    have h2 : polyTInclude (K := K) n q * c -
        polyTInclude (K := K) n q *
          (Finsupp.linearCombination (DefRing n K)
            (Subtype.val : ↑(tildeJGenerators G) → DefRing n K)) g ∈ tildeJ (K := K) G :=
      Ideal.sub_mem _ hmul h1
    have hfactor : polyTInclude (K := K) n q * c -
        polyTInclude (K := K) n q *
          (Finsupp.linearCombination (DefRing n K)
            (Subtype.val : ↑(tildeJGenerators G) → DefRing n K)) g =
        polyTInclude (K := K) n q * r := by
      rw [hdecomp]; ring
    rw [hfactor] at h2
    exact h2
  -- Support of `polyTInclude q * r` inherits "standard" from r.
  have hprod_supp : ∀ α ∈ (polyTInclude (K := K) n q * r).support,
      ∀ (i j : Fin n), G.Adj i j → i < j →
        ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α) :=
    polyTInclude_mul_support_avoids q r hrSupp
  -- Apply Gröbner basis property.
  have hprod_zero : polyTInclude (K := K) n q * r = 0 :=
    tildeJ_gbProperty hClosed _ hprod_mem hprod_supp
  -- DefRing is a domain, polyTInclude q ≠ 0 (rename is injective, q ≠ 0), so r = 0.
  have hpoly_ne : polyTInclude (K := K) n q ≠ 0 := by
    change MvPolynomial.rename (Sum.inr : Unit → DefVars n) q ≠ 0
    intro h
    exact hq (MvPolynomial.rename_injective _ Sum.inr_injective (by rw [h]; simp))
  have hrzero : r = 0 := by
    rcases mul_eq_zero.mp hprod_zero with h | h
    · exact absurd h hpoly_ne
    · exact h
  rw [hrzero, add_zero] at hdecomp
  rw [hdecomp]; exact hgmem

/-- **R1.d (refined)**: the deformation `S[t] ⧸ Ĩ` is flat as a `K[t]`-module.

    The proof reduces to the colon-ideal sub-sorry `tildeJ_polyT_colon_eq`
    via two Mathlib principles:

    - `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`: over a Dedekind
      domain (here `PolyT K = K[t]`, which is a PID hence Dedekind), being
      torsion-free implies being flat.
    - `Module.IsTorsionFree.mk`: torsion-freeness is constructed from
      `∀ r, IsRegular r → IsSMulRegular M r`.

    For `R = PolyT K` a domain, `IsRegular r ↔ r ≠ 0`, and `IsSMulRegular` of
    `r` on `DefRing n K ⧸ Ĩ` unfolds (via the algebra structure and quotient
    laws) to exactly the statement `tildeJ_polyT_colon_eq`. -/
theorem tildeJ_flat_over_polyT
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G) :
    Module.Flat (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) := by
  -- It suffices to show torsion-freeness over the Dedekind domain `PolyT K`.
  haveI hTF : Module.IsTorsionFree (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) := by
    refine Module.IsTorsionFree.mk ?_
    intro q hReg
    -- `q` is a nonzero element of `PolyT K` (a domain).
    have hqne : q ≠ 0 := hReg.ne_zero
    -- `IsSMulRegular` for scalar mul by `q` on the quotient.
    intro c d hcd
    change q • c = q • d at hcd
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Algebra.smul_def, Algebra.smul_def] at hcd
    -- Rewrite `algebraMap (PolyT K) (quot) q = mk (polyTInclude n q)`.
    have hAlg : algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) q
        = (Ideal.Quotient.mk (tildeJ (K := K) G)) (polyTInclude (K := K) n q) := by
      rw [← Ideal.Quotient.mk_comp_algebraMap]
      rfl
    rw [hAlg, ← map_mul, ← map_mul, Ideal.Quotient.eq] at hcd
    rw [Ideal.Quotient.eq]
    have hfactor :
        polyTInclude (K := K) n q * c' - polyTInclude (K := K) n q * d'
          = polyTInclude (K := K) n q * (c' - d') := by ring
    rw [hfactor] at hcd
    exact tildeJ_polyT_colon_eq hClosed q hqne _ hcd
  -- Torsion-free + Dedekind ⟹ Flat (Mathlib instance).
  infer_instance

/-- Scalar multiplication by `X () - 1 ∈ K[t]` on `S[t] ⧸ Ĩ` agrees with
    ring multiplication by the class of `tDef n - 1`. -/
private lemma polyT_tMinusOne_smul_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (m : DefRing n K ⧸ tildeJ (K := K) G) :
    algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) (X () - 1) • m =
      ((X () - 1 : PolyT K)) • m :=
  algebraMap_smul _ _ m

/-- Scalar multiplication by `X () ∈ K[t]` on `S[t] ⧸ Ĩ` agrees with
    ring multiplication by the class of `tDef n`. -/
private lemma polyT_t_smul_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (m : DefRing n K ⧸ tildeJ (K := K) G) :
    algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) (X ()) • m =
      ((X () : PolyT K)) • m :=
  algebraMap_smul _ _ m

/-- **R1.d (the technical heart of R1)**: `(t - 1)` is a non-zero-divisor on
    the deformation `S[t] ⧸ Ĩ`.

    Classical proof (Eisenbud 15.17): `K[t]` is a PID, so flatness of
    `S[t] ⧸ Ĩ` over `K[t]` is equivalent to `t`-torsion-freeness, and a flat
    module over a domain is torsion-free over any nonzero element. Since
    `{f̃_{i,j}}` is a Gröbner basis of `Ĩ` whose leading terms `x_i y_j`
    contain no `t`, the standard normal form in `S[t] ⧸ Ĩ` is `K[t]`-free on
    the standard monomials of `J_G`.

    The proof transfers the regularity of `t - 1 ∈ K[t]` to the quotient via
    the flatness lemma `tildeJ_flat_over_polyT`. -/
theorem tildeJ_tMinusOne_isSMulRegular {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) :
    IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1)) := by
  -- `t - 1 ∈ K[t]` is nonzero (evaluating at `0` gives `-1 ≠ 0`), hence regular.
  have hReg : IsRegular ((X () - 1 : PolyT K)) := by
    refine IsRegular.of_ne_zero' ?_
    intro h
    have := congrArg (eval (fun _ : Unit => (0 : K))) h
    simp at this
  haveI : Module.Flat (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_flat_over_polyT hClosed
  have h1 : IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G) ((X () - 1 : PolyT K)) :=
    Module.Flat.isSMulRegular_of_isRegular hReg
  -- Translate `PolyT K`-scalar multiplication by `X () - 1` into ring multiplication
  -- by the class of `tDef n - 1`.
  rw [← algebraMap_polyT_tMinusOne G]
  rw [isSMulRegular_map
    (algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G))]
  · exact h1
  · intro m; exact polyT_tMinusOne_smul_eq G m

/-- **R1.d companion**: `t` is a non-zero-divisor on the deformation
    `S[t] ⧸ Ĩ`. This is the `t = 0` fiber analogue of
    `tildeJ_tMinusOne_isSMulRegular` and is proved uniformly from flatness
    of `S[t] ⧸ Ĩ` over `K[t]`: `t ∈ K[t]` is nonzero (hence regular), and
    flat modules are torsion-free. -/
theorem tildeJ_t_isSMulRegular {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) :
    IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n)) := by
  have hReg : IsRegular ((X () : PolyT K)) := by
    refine IsRegular.of_ne_zero' ?_
    exact MvPolynomial.X_ne_zero _
  haveI : Module.Flat (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_flat_over_polyT hClosed
  have h1 : IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G) ((X () : PolyT K)) :=
    Module.Flat.isSMulRegular_of_isRegular hReg
  rw [← algebraMap_polyT_t G]
  rw [isSMulRegular_map
    (algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G))]
  · exact h1
  · intro m; exact polyT_t_smul_eq G m

/-! ## R1.f.1: local and global CM of the deformation -/

/-- **R1.f.1 sub-statement**: local Cohen–Macaulayness of the deformation at
the irrelevant ideal. This is the first half of the R1.f.1 chain; the rest
— the graded local-to-global theorem — is provided by
`toMathlib/GradedCM.lean`.

Proof: the deformation parameter `t` is a regular element on `S[t] ⧸ Ĩ`
(`tildeJ_t_isSMulRegular`); the quotient by the class of `t` is `S ⧸
monomialInitialIdeal G` (via `DoubleQuot.quotQuotEquivQuotSup` +
`specZeroQuotEquiv`), which is CM globally by Step 1. Localising at the
irrelevant ideal and applying `isCohenMacaulayLocalRing_of_regular_quotient`
closes this step. -/
theorem tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    haveI :=
      (GradedIrrelevant.irrelevant_isMaximal (tildeJQuotGrading (K := K) G)
        (tildeJQuotGrading_connectedGraded G)).isPrime
    IsCohenMacaulayLocalRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant (tildeJQuotGrading (K := K) G)).toIdeal) := by
  haveI : IsNoetherianRing (DefRing n K ⧸ tildeJ (K := K) G) :=
    Ideal.Quotient.isNoetherianRing _
  haveI hmMax :
      (HomogeneousIdeal.irrelevant (tildeJQuotGrading (K := K) G)).toIdeal.IsMaximal :=
    GradedIrrelevant.irrelevant_isMaximal _ (tildeJQuotGrading_connectedGraded G)
  haveI hmPrime := hmMax.isPrime
  -- Name the players.
  set A := DefRing n K ⧸ tildeJ (K := K) G
  set m : Ideal A :=
    (HomogeneousIdeal.irrelevant (tildeJQuotGrading (K := K) G)).toIdeal
  set L := Localization.AtPrime m
  set t_A : A := Ideal.Quotient.mk (tildeJ (K := K) G) (tDef n) with ht_A_def
  set t_L : L := algebraMap A L t_A with ht_L_def
  haveI : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  -- (1) t_A ∈ m.
  have ht_A_mem_m : t_A ∈ m := tDefClass_mem_irrelevant G
  -- (2) t_L ∈ maximalIdeal L.
  have ht_L_mem_max : t_L ∈ IsLocalRing.maximalIdeal L := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ ht_A_mem_m
  -- (3) t_A is regular on A.
  have ht_A_reg : IsSMulRegular A t_A := tildeJ_t_isSMulRegular hClosed
  -- (4) t_L is regular on L (localization is flat).
  have ht_L_reg : IsSMulRegular L t_L := ht_A_reg.of_flat
  -- (5) A ⧸ span{t_A} is globally CM via the iso to S ⧸ monomialInitialIdeal G.
  have hspan_map_eq :
      Ideal.map (Ideal.Quotient.mk (tildeJ (K := K) G)) (Ideal.span {tDef n}) =
      Ideal.span ({t_A} : Set A) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hEq1 :
      A ⧸ Ideal.map (Ideal.Quotient.mk (tildeJ (K := K) G)) (Ideal.span {tDef n}) ≃+*
        DefRing n K ⧸ zeroSumIdeal (K := K) G :=
    DoubleQuot.quotQuotEquivQuotSup _ _
  have hEq2 :
      DefRing n K ⧸ zeroSumIdeal (K := K) G ≃+*
        MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G :=
    (specZeroQuotEquiv (K := K) G).symm
  haveI hCM_Aquot : IsCohenMacaulayRing (A ⧸ Ideal.span ({t_A} : Set A)) := by
    rw [← hspan_map_eq]
    exact isCohenMacaulayRing_of_ringEquiv (hEq1.trans hEq2).symm
  -- (6) p' := image of m in A/(t_A) is prime; localize at it gives CM.
  set p' : Ideal (A ⧸ Ideal.span ({t_A} : Set A)) :=
    Ideal.map (Ideal.Quotient.mk (Ideal.span ({t_A} : Set A))) m with hp'_def
  haveI hp'_prime : p'.IsPrime := by
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht_A_mem_m
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
    IsCohenMacaulayRing.CM_localize p'
  -- (7) QuotSMulTop t_L L ≃+* Localization.AtPrime p' via
  -- `quotSMulTopLocalizationEquiv_of_mem`.
  have hp'_comap :
      p'.comap (Ideal.Quotient.mk (Ideal.span ({t_A} : Set A))) = m := by
    rw [hp'_def, Ideal.comap_map_quotientMk]
    refine sup_eq_right.mpr ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht_A_mem_m
  have h_qsm_equiv : QuotSMulTop t_L L ≃+* Localization.AtPrime p' :=
    quotSMulTopLocalizationEquiv_of_mem ht_A_mem_m hp'_comap
  haveI : IsLocalRing (QuotSMulTop t_L L) := quotSMulTopLocalRing ht_L_mem_max
  haveI : IsCohenMacaulayLocalRing (QuotSMulTop t_L L) :=
    isCohenMacaulayLocalRing_of_ringEquiv' inferInstance h_qsm_equiv.symm
  -- (8) Conclude via `isCohenMacaulayLocalRing_of_regular_quotient`.
  exact isCohenMacaulayLocalRing_of_regular_quotient ht_L_reg ht_L_mem_max
    IsCohenMacaulayLocalRing.depth_eq_dim

/-- **R1.f.1**: the global Cohen–Macaulayness of the deformation `S[t] ⧸ Ĩ`.

Classical chain (graded local-to-global): the weight grading
`w(x_i) = 2(n+1-i)`, `w(y_j) = (n+1-j)`, `w(t) = 1` makes `Ĩ` weighted-
homogeneous, so `S[t] ⧸ Ĩ` is a connected ℕ-graded `K`-algebra. Local CM
at the irrelevant ideal (via `tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant`)
combined with the graded local-to-global theorem
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant` from
`toMathlib/GradedCM.lean`
yields global CM. -/
theorem tildeJ_quotient_isCohenMacaulay
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing (DefRing n K ⧸ tildeJ (K := K) G) := by
  haveI : IsNoetherianRing (DefRing n K ⧸ tildeJ (K := K) G) :=
    Ideal.Quotient.isNoetherianRing _
  exact GradedCM.isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant
    (tildeJQuotGrading (K := K) G)
    (tildeJQuotGrading_connectedGraded G)
    (tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant hClosed hCM)

/-! ## R1.f assembly: composing the four-arrow chain -/

theorem groebnerDeformation_cm_transfer
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  -- Step 1 + 2: global CM of S[t]/Ĩ; (t - 1) regular on it.
  haveI hCMext : IsCohenMacaulayRing (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_quotient_isCohenMacaulay hClosed hCM
  have hreg : IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1)) :=
    tildeJ_tMinusOne_isSMulRegular hClosed
  -- Step 3: descent through regular element.
  have hCMdouble : IsCohenMacaulayRing
      ((DefRing n K ⧸ tildeJ (K := K) G) ⧸
       Ideal.span ({Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1)} : Set _)) :=
    isCohenMacaulayRing_quotient_of_smulRegular hreg
  -- Step 4a: DoubleQuot identifies the inner double quotient with DefRing/(Ĩ ⊔ {t-1}).
  have hSpan_eq : (Ideal.span ({Ideal.Quotient.mk (tildeJ (K := K) G)
        (tDef (K := K) n - 1)} : Set _) : Ideal _) =
      Ideal.map (Ideal.Quotient.mk (tildeJ (K := K) G))
        (Ideal.span {tDef (K := K) n - 1}) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hSpan_eq] at hCMdouble
  haveI := hCMdouble
  haveI hCMsup : IsCohenMacaulayRing
      (DefRing n K ⧸ (tildeJ (K := K) G ⊔ Ideal.span {tDef (K := K) n - 1})) :=
    isCohenMacaulayRing_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotSup
        (tildeJ (K := K) G) (Ideal.span ({tDef (K := K) n - 1} : Set _)))
  -- Step 4b: baseQuotEquiv transports CM back to S/J_G.
  exact isCohenMacaulayRing_of_ringEquiv (baseQuotEquiv (K := K) G).symm

end
