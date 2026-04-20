import BEI.Equidim
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Algebra.MvPolynomial.Equiv

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

/-- The deformation ring `S[t] = K[x, y, t]` for the BEI Gröbner deformation of
    `J_G ⊂ MvPolynomial (BinomialEdgeVars (Fin n)) K`. Variables:

    - `Sum.inl (Sum.inl i)` is `x_i` for `i : Fin n`;
    - `Sum.inl (Sum.inr j)` is `y_j` for `j : Fin n`;
    - `Sum.inr ()` is the deformation parameter `t`. -/
abbrev DefRing (n : ℕ) (K : Type) [Field K] : Type :=
  MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K

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
  show aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specZero_X_inr (n : ℕ) (u : Unit) :
    specZero (K := K) n (X (Sum.inr u)) = 0 := by
  show aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specOne_X_inl (n : ℕ) (v : BinomialEdgeVars (Fin n)) :
    specOne (K := K) n (X (Sum.inl v)) = X v := by
  show aeval _ _ = _; rw [aeval_X]; rfl

@[simp] lemma specOne_X_inr (n : ℕ) (u : Unit) :
    specOne (K := K) n (X (Sum.inr u)) = 1 := by
  show aeval _ _ = _; rw [aeval_X]; rfl

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
  show specOne (K := K) n (X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j)) -
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
  show specZero (K := K) n (X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j)) -
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
    show specOne n (fijTilde i j) = _
    exact specOne_fijTilde i j
  · rintro ⟨i, j, hadj, hij, rfl⟩
    refine ⟨fijTilde i j, ⟨i, j, hadj, hij, rfl⟩, ?_⟩
    show specOne n (fijTilde i j) = _
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
    show specZero n (fijTilde i j) = _
    rw [specZero_fijTilde i j hij]
    rfl
  · rintro ⟨i, j, hadj, hij, rfl⟩
    refine ⟨fijTilde i j, ⟨i, j, hadj, hij, rfl⟩, ?_⟩
    show specZero n (fijTilde i j) = _
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
    show baseInclude (K := K) n (x i * y j - x j * y i) = _
    simp only [baseInclude, x, y, map_sub, map_mul, AlgHom.coe_toRingHom, rename_X]
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
-- because of the deeply-nested types `MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K`.
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
    show (specOne n) ((baseInclude n) (C r)) = C r
    rw [show (baseInclude (K := K) n) (C r) = C r from by simp [baseInclude],
        show (specOne (K := K) n) (C r) = C r from by simp [specOne]]
  | add p q hp hq =>
    show (specOne n) ((baseInclude n) (p + q)) = p + q
    rw [map_add, map_add, hp, hq]
  | mul_X p v ih =>
    show (specOne n) ((baseInclude n) (p * X v)) = p * X v
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
private lemma quot_baseInclude_specOne_X (v : BinomialEdgeVars (Fin n) ⊕ Unit) :
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
    have hmem : (1 : DefRing n K) - X (Sum.inr ()) = -(tDef n - 1) := by
      show (1 : DefRing n K) - X (Sum.inr ()) = -(X (Sum.inr ()) - 1)
      ring
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
  rename (Sum.inr : Unit → BinomialEdgeVars (Fin n) ⊕ Unit)

@[simp] lemma polyTInclude_X (n : ℕ) (u : Unit) :
    polyTInclude (K := K) n (X u) = X (Sum.inr u) := by
  show rename _ _ = _
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

/-- The `BinomialEdgeVars (Fin n) ⊕ Unit` type is finite. -/
instance defVars_Finite (n : ℕ) :
    Finite (BinomialEdgeVars (Fin n) ⊕ Unit) := by
  unfold BinomialEdgeVars; infer_instance

/-- Linear order on the deformation variable type `BinomialEdgeVars (Fin n) ⊕ Unit`:
    the paper's `x > y` order on `BinomialEdgeVars (Fin n)` with `t = inr ()`
    strictly below every `x` and `y`. -/
@[reducible] def defLE {n : ℕ} (a b : BinomialEdgeVars (Fin n) ⊕ Unit) : Prop :=
  match a, b with
  | Sum.inl u, Sum.inl v => (u : BinomialEdgeVars (Fin n)) ≤ v
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => True

instance defVars_LinearOrder (n : ℕ) :
    LinearOrder (BinomialEdgeVars (Fin n) ⊕ Unit) where
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
    cases a <;> cases b <;> simp_all only [defLE, Sum.inl.injEq]
    exact le_antisymm h1 h2
  le_total a b := by
    cases a <;> cases b <;> simp only [defLE]
    · exact le_total _ _
    · exact Or.inr trivial
    · exact Or.inl trivial
    · exact Or.inl trivial

instance defVars_WellFoundedGT (n : ℕ) :
    @WellFoundedGT (BinomialEdgeVars (Fin n) ⊕ Unit) (defVars_LinearOrder n).toLT :=
  @Finite.to_wellFoundedGT _ (defVars_Finite n) (defVars_LinearOrder n).toPreorder

/-- The lex monomial order on the deformation variable type. Under this order,
    the leading monomial of `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i` is
    `x_i y_j` (for `i < j`), with leading coefficient `1`. -/
noncomputable def deformationMonomialOrder (n : ℕ) :
    MonomialOrder (BinomialEdgeVars (Fin n) ⊕ Unit) :=
  @MonomialOrder.lex (BinomialEdgeVars (Fin n) ⊕ Unit)
    (defVars_LinearOrder n) (defVars_WellFoundedGT n)

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

/-! ## Sub-sorries of R1 -/

/-- **R1.f.1**: the global Cohen–Macaulayness of the deformation `S[t] ⧸ Ĩ`.

    Classical chain (graded local-to-global): the weight grading
    `w(x_i) = 2(n+1-i)`, `w(y_j) = (n+1-j)`, `w(t) = 1` makes `Ĩ` weighted-
    homogeneous of degree 2, so `S[t] ⧸ Ĩ` is a connected ℕ-graded `K`-algebra.
    Local CM at the irrelevant ideal follows from Step 1 + the regular-quotient
    lift through `t` (which is regular by R1.d). Global CM then follows from
    `toMathlib/GradedCM.lean`'s `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`
    (which has one open Case-C sorry that may need to be closed or routed
    around).

    **Status**: not yet formalized. -/
theorem tildeJ_quotient_isCohenMacaulay
    {n : ℕ} (G : SimpleGraph (Fin n))
    (_hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing (DefRing n K ⧸ tildeJ (K := K) G) := by
  sorry

/-- **R1.d colon-ideal sub-sorry**: for every nonzero polynomial `q ∈ K[t]`,
    the ideal `Ĩ` is saturated with respect to `polyTInclude q`.

    This is the BEI-specific content of `tildeJ_flat_over_polyT`: since
    `PolyT K = K[t]` is a PID, flatness of `DefRing n K ⧸ Ĩ` over `PolyT K`
    reduces to torsion-freeness, which in turn reduces to the statement below
    (via `Module.IsTorsionFree.mk` together with the fact that in a domain
    every regular element is nonzero).

    Classical proof (Eisenbud 15.17): `{f̃_{i,j}}` is a Gröbner basis of `Ĩ`
    whose leading terms `x_i y_j` contain no `t`. The normal form of any
    `c ∈ DefRing n K` modulo `Ĩ` is a `K[t]`-linear combination of standard
    monomials of `J_G`. Multiplying by `polyTInclude q` (a pure-`t` polynomial)
    preserves the "standard monomial" support. If `polyTInclude q · c ∈ Ĩ`,
    the product's normal form is zero, so each `K[t]`-coefficient times `q` is
    zero; by `K[t]`-domain and `q ≠ 0`, each coefficient is zero, hence the
    normal form of `c` is zero, i.e. `c ∈ Ĩ`.

    **Status**: not yet formalized. This is the single remaining paper-critical
    sorry on the R1.d branch, and by design is a purely BEI-specific Gröbner
    statement rather than a general commutative-algebra one. -/
theorem tildeJ_polyT_colon_eq
    {n : ℕ} (G : SimpleGraph (Fin n))
    (q : PolyT K) (_hq : q ≠ 0)
    (c : DefRing n K) (_hmul : polyTInclude (K := K) n q * c ∈ tildeJ (K := K) G) :
    c ∈ tildeJ (K := K) G := by
  sorry

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
    {n : ℕ} (G : SimpleGraph (Fin n)) :
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
    exact tildeJ_polyT_colon_eq G q hqne _ hcd
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
theorem tildeJ_tMinusOne_isSMulRegular {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1)) := by
  -- `t - 1 ∈ K[t]` is nonzero (evaluating at `0` gives `-1 ≠ 0`), hence regular.
  have hReg : IsRegular ((X () - 1 : PolyT K)) := by
    refine IsRegular.of_ne_zero' ?_
    intro h
    have := congrArg (eval (fun _ : Unit => (0 : K))) h
    simp at this
  haveI : Module.Flat (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_flat_over_polyT G
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
theorem tildeJ_t_isSMulRegular {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n)) := by
  have hReg : IsRegular ((X () : PolyT K)) := by
    refine IsRegular.of_ne_zero' ?_
    exact MvPolynomial.X_ne_zero _
  haveI : Module.Flat (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_flat_over_polyT G
  have h1 : IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G) ((X () : PolyT K)) :=
    Module.Flat.isSMulRegular_of_isRegular hReg
  rw [← algebraMap_polyT_t G]
  rw [isSMulRegular_map
    (algebraMap (PolyT K) (DefRing n K ⧸ tildeJ (K := K) G))]
  · exact h1
  · intro m; exact polyT_t_smul_eq G m

/-! ## R1.f assembly: composing the four-arrow chain

This is a closed proof modulo three sub-sorries:
- `tildeJ_quotient_isCohenMacaulay` (graded local-to-global step);
- `tildeJ_tMinusOne_isSMulRegular` (flatness step);
- `baseQuotEquiv` (routine iso plumbing).
-/
theorem groebnerDeformation_cm_transfer
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  -- Step 1 + 2: global CM of S[t]/Ĩ; (t - 1) regular on it.
  haveI hCMext : IsCohenMacaulayRing (DefRing n K ⧸ tildeJ (K := K) G) :=
    tildeJ_quotient_isCohenMacaulay G hCM
  have hreg : IsSMulRegular (DefRing n K ⧸ tildeJ (K := K) G)
      (Ideal.Quotient.mk (tildeJ (K := K) G) (tDef (K := K) n - 1)) :=
    tildeJ_tMinusOne_isSMulRegular G
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
