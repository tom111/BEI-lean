import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Helper lemmas for ideal quotients

This file collects small ring-theoretic lemmas about quotient rings, double
quotients, and the bridge between `QuotSMulTop x R` and `R ⧸ Ideal.span {x}`.

These were originally `private` inside `BEI/Equidim.lean`; they are
formulated in terms of arbitrary commutative rings only and so live here
as candidates for upstreaming.

## Main results

- `mem_map_mk_iff_mem_sup`: `mk_I x ∈ J.map mk_I ↔ x ∈ I ⊔ J`.
- `isSMulRegular_of_doubleQuot`: NZD on `R ⧸ (I ⊔ J)` transfers to NZD on the
  iterated quotient `(R ⧸ I) ⧸ J.map mk_I`.
- `Ideal.smul_top_eq_restrictScalars`: `I • ⊤ = I` as a submodule of `R`.
- `Ideal.ofList_map`: `Ideal.ofList` commutes with ring homomorphism maps.
- `Ideal.ofList_take_map_mk_smul_top`: identifies the step-`i` module quotient
  in `IsWeaklyRegular` on the self-module of `R ⧸ I` with a double quotient.
- `Submodule.smul_top_eq_span_singleton`: `(x • ⊤ : Submodule R R) = span {x}`
  viewed as ideals.
- `quotSMulTopRingEquivIdealQuotient`:
  `QuotSMulTop x R ≃+* R ⧸ Ideal.span {x}`.
-/

variable {R : Type*} [CommRing R]

/-! ## Membership in `J.map (Ideal.Quotient.mk I)` -/

/-- Membership in `J.map mk_I` is equivalent to membership in `I ⊔ J`. -/
lemma mem_map_mk_iff_mem_sup {I J : Ideal R} (x : R) :
    Ideal.Quotient.mk I x ∈ J.map (Ideal.Quotient.mk I) ↔ x ∈ I ⊔ J := by
  constructor
  · intro h
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
    obtain ⟨j, hj, hjx⟩ := h
    rw [Ideal.Quotient.eq] at hjx
    have : x - j ∈ I := by
      rw [show x - j = -(j - x) from by ring]; exact I.neg_mem hjx
    rw [show x = (x - j) + j from by ring]
    exact (I ⊔ J).add_mem (Ideal.mem_sup_left this) (Ideal.mem_sup_right hj)
  · intro h
    have : Ideal.Quotient.mk I x ∈ (I ⊔ J).map (Ideal.Quotient.mk I) :=
      Ideal.mem_map_of_mem _ h
    rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at this

/-- Transfer of `IsSMulRegular` through double quotient: if `r` is a NZD on
`R ⧸ (I ⊔ J)`, then `mk_I(r)` is a NZD on `(R ⧸ I) ⧸ J.map mk_I`
(where the scalar action uses the `R ⧸ I`-algebra structure). -/
lemma isSMulRegular_of_doubleQuot {I J : Ideal R} {r : R}
    (hreg : IsSMulRegular (R ⧸ (I ⊔ J)) (Ideal.Quotient.mk (I ⊔ J) r)) :
    IsSMulRegular ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (Ideal.Quotient.mk I r) := by
  set mkI := Ideal.Quotient.mk I
  set mkIJ := Ideal.Quotient.mk (I ⊔ J)
  set mkJ' := Ideal.Quotient.mk (Ideal.map mkI J)
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a'', rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨b'', rfl⟩ := Ideal.Quotient.mk_surjective b'
  change mkI r • mkJ' (mkI a'') = mkI r • mkJ' (mkI b'') at hab
  simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hab
  have hab' : mkJ' (mkI (r * a'')) = mkJ' (mkI (r * b'')) := by
    rwa [map_mul mkI r a'', map_mul mkI r b'']
  rw [Ideal.Quotient.eq, ← map_sub, mem_map_mk_iff_mem_sup,
      show r * a'' - r * b'' = r * (a'' - b'') from by ring] at hab'
  rw [Ideal.Quotient.eq, ← map_sub, mem_map_mk_iff_mem_sup]
  have h1 : mkIJ r * mkIJ (a'' - b'') = 0 := by
    rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hab'
  have h2 := hreg (show mkIJ r • mkIJ (a'' - b'') = mkIJ r • 0 from by
    rw [smul_eq_mul, smul_zero]; exact h1)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

/-! ## `I • ⊤` and `Ideal.ofList` helpers -/

namespace Ideal

/-- For the self-module of a ring, `I • ⊤ = I.restrictScalars R`. -/
lemma smul_top_self_eq_restrictScalars (I : Ideal R) :
    I • (⊤ : Submodule R R) = I.restrictScalars R := by
  rw [Ideal.smul_top_eq_map, show algebraMap R R = RingHom.id R from rfl,
      Ideal.map_id]

/-- `Ideal.ofList` commutes with ring homomorphism maps. -/
lemma ofList_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (rs : List R) :
    (Ideal.ofList rs).map f = Ideal.ofList (rs.map f) := by
  simp only [Ideal.ofList, Ideal.map_span]
  congr 1; ext x; simp [List.mem_map]

/-- The step-`i` module quotient in `IsWeaklyRegular` on the self-module
of `R ⧸ I` matches the double quotient `(R ⧸ I) ⧸ J.map mk_I`. -/
lemma ofList_take_map_mk_smul_top {I : Ideal R} (rs : List R) (i : ℕ) :
    Ideal.ofList (List.take i (rs.map (Ideal.Quotient.mk I))) •
      (⊤ : Submodule (R ⧸ I) (R ⧸ I)) =
    ((Ideal.ofList (List.take i rs)).map
      (Ideal.Quotient.mk I)).restrictScalars (R ⧸ I) := by
  rw [smul_top_self_eq_restrictScalars]; congr 1
  rw [← List.map_take, Ideal.ofList_map]

end Ideal

/-! ## Bridge between `QuotSMulTop` and `R ⧸ Ideal.span {x}` -/

open scoped Pointwise

/-- Bridging lemma: `(x • ⊤ : Submodule R R) = Ideal.span {x}` as ideals. This
lets us identify `QuotSMulTop x R` with `R ⧸ Ideal.span {x}`. -/
lemma Submodule.smul_top_eq_span_singleton (x : R) :
    ((x • (⊤ : Submodule R R)) : Ideal R) = Ideal.span {x} := by
  apply le_antisymm
  · rintro y ⟨z, _, rfl⟩
    change (DistribSMul.toLinearMap R R x) z ∈ Ideal.span {x}
    exact Ideal.mem_span_singleton'.mpr ⟨z, by simp [mul_comm]⟩
  · intro y hy
    rcases Ideal.mem_span_singleton'.mp hy with ⟨z, rfl⟩
    refine ⟨z, Submodule.mem_top, ?_⟩
    change (DistribSMul.toLinearMap R R x) z = z * x
    simp [mul_comm]

/-- Ring equivalence between the two quotient views:
`QuotSMulTop x R ≃+* R ⧸ Ideal.span {x}`. Since `Ideal R = Submodule R R`
definitionally, this is just `Ideal.quotEquivOfEq` applied to
`Submodule.smul_top_eq_span_singleton`. -/
noncomputable def quotSMulTopRingEquivIdealQuotient (x : R) :
    QuotSMulTop x R ≃+* R ⧸ Ideal.span {x} :=
  Ideal.quotEquivOfEq (Submodule.smul_top_eq_span_singleton x)
