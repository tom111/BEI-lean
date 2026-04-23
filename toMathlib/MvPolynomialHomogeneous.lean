import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Graded contraction for `MvPolynomial`

A homogeneous ideal `I ⊆ MvPolynomial σ K` is closed under taking homogeneous
components.  If `f * g ∈ I` and `f` has invertible constant coefficient, then
`g ∈ I`.  Equivalently: in the quotient `MvPolynomial σ K ⧸ I`, every element
with invertible constant coefficient is a non-zero-divisor.

These were originally `private` inside `BEI/Equidim.lean`.

## Main results

- `MvPolynomial.homogeneousComponent_mul_eq_zero_of_low_degrees`:
  the `d`-th homogeneous component of `f * g` vanishes when `constantCoeff f = 0`
  and all components of `g` of degree `< d` vanish.
- `MvPolynomial.homogeneousComponent_sum_low`:
  the `j`-th homogeneous component of a partial sum of low-degree components
  recovers the original component, for `j < d`.
- `MvPolynomial.mem_of_mul_mem_of_isUnit_constantCoeff`:
  the graded contraction lemma.
-/

namespace MvPolynomial

variable {σ : Type*}

/-- Degree-counting lemma for the lowest component of a product: if
`constantCoeff f = 0` and the components of `g` of degree `< d` vanish, then
`homogeneousComponent d (f * g) = 0`. -/
lemma homogeneousComponent_mul_eq_zero_of_low_degrees
    {R : Type*} [CommSemiring R]
    {f g : MvPolynomial σ R} {d : ℕ}
    (hf : constantCoeff f = 0)
    (hg : ∀ j < d, homogeneousComponent j g = 0) :
    homogeneousComponent d (f * g) = 0 := by
  classical
  ext m
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hmd
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : a = 0
    · simp [ha, ← constantCoeff_eq, hf]
    · have hab_deg : a.degree + b.degree = d := by
        rw [← Finsupp.degree.map_add, hab]; exact hmd
      have ha_pos : 0 < a.degree := by
        rw [pos_iff_ne_zero]; exact fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
      have hb_lt : b.degree < d := by omega
      have : coeff b g = 0 := by
        have := congr_arg (coeff b) (hg b.degree hb_lt)
        rwa [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at this
      rw [this, mul_zero]
  · rfl

/-- The `j`-th homogeneous component of a partial sum of low-degree components
of `g` recovers `homogeneousComponent j g`, provided `j < d`. -/
lemma homogeneousComponent_sum_low
    {R : Type*} [CommSemiring R]
    (g : MvPolynomial σ R) (d : ℕ) {j : ℕ} (hj : j < d) :
    homogeneousComponent j
      (∑ k ∈ Finset.range d, homogeneousComponent k g) =
    homogeneousComponent j g := by
  rw [_root_.map_sum (homogeneousComponent j)]
  simp_rw [homogeneousComponent_of_mem (homogeneousComponent_mem _ g)]
  exact (Finset.sum_ite_eq (Finset.range d) j _).trans
    (if_pos (Finset.mem_range.mpr hj))

/-- **Graded contraction lemma for `MvPolynomial`**: if `I` is a homogeneous
ideal (closed under taking homogeneous components), `f * g ∈ I`, and
`constantCoeff f` is a unit, then `g ∈ I`.

Equivalently: in `MvPolynomial σ K ⧸ I`, any element with invertible constant
coefficient is a non-zero-divisor.

The proof works by strong induction on the degree: at each step,
subtracting the already-proved low-degree components and using the
degree-counting lemma `homogeneousComponent_mul_eq_zero_of_low_degrees`
shows that the unit constant coefficient of `f` forces each successive
homogeneous component of `g` into `I`. -/
theorem mem_of_mul_mem_of_isUnit_constantCoeff
    {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)}
    (hI_hom : ∀ p ∈ I, ∀ (d : ℕ), homogeneousComponent d p ∈ I)
    {f g : MvPolynomial σ K}
    (hfg : f * g ∈ I)
    (hf : IsUnit (constantCoeff f)) :
    g ∈ I := by
  classical
  suffices h : ∀ d, homogeneousComponent d g ∈ I by
    rw [show g = ∑ i ∈ Finset.range (g.totalDegree + 1),
      homogeneousComponent i g from (sum_homogeneousComponent g).symm]
    exact I.sum_mem (fun d _ => h d)
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    set c := constantCoeff f
    set g_low := ∑ j ∈ Finset.range d, homogeneousComponent j g
    have hg_low_mem : g_low ∈ I :=
      I.sum_mem (fun j hj => ih j (Finset.mem_range.mp hj))
    have hg_high_vanish : ∀ j < d,
        homogeneousComponent j (g - g_low) = 0 := by
      intro j hj
      rw [map_sub, homogeneousComponent_sum_low g d hj, sub_self]
    have hcomp_eq : homogeneousComponent d (g - g_low) = homogeneousComponent d g := by
      rw [map_sub]
      have : homogeneousComponent d g_low = 0 := by
        rw [_root_.map_sum (homogeneousComponent d)]
        simp_rw [homogeneousComponent_of_mem (homogeneousComponent_mem _ g)]
        exact Finset.sum_eq_zero
          (fun k hk => if_neg (by rw [Finset.mem_range] at hk; omega))
      rw [this, sub_zero]
    have hfg_high : f * (g - g_low) ∈ I := by
      rw [mul_sub]; exact I.sub_mem hfg (I.mul_mem_left f hg_low_mem)
    set f' := f - C c
    have hf'_cc : constantCoeff f' = 0 := by simp [f', c]
    have hvanish : homogeneousComponent d (f' * (g - g_low)) = 0 :=
      homogeneousComponent_mul_eq_zero_of_low_degrees hf'_cc hg_high_vanish
    have hcomp_fgh : homogeneousComponent d (f * (g - g_low)) ∈ I :=
      hI_hom _ hfg_high d
    have hCcg : C c * homogeneousComponent d g ∈ I := by
      have : f * (g - g_low) = C c * (g - g_low) + f' * (g - g_low) := by ring
      rw [this, map_add, hvanish, add_zero, homogeneousComponent_C_mul, hcomp_eq] at hcomp_fgh
      exact hcomp_fgh
    exact (Submodule.smul_mem_iff_of_isUnit I (RingHom.isUnit_map C hf)).mp hCcg

end MvPolynomial
