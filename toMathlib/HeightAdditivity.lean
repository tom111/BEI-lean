/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Height additivity for ideals in disjoint variable sets

For prime ideals I₁ ⊆ K[X₁] and I₂ ⊆ K[X₂] in disjoint variable sets:
  `height(I₁ + I₂) = height(I₁) + height(I₂)` in K[X₁, X₂]

This is a standard result in commutative algebra, following from the
going-down property for flat extensions.

## Main results

- `MvPolynomial.height_sup_disjoint`: heights add for disjoint-variable primes

## Proof strategy

1. `MvPolynomial σ R` is free over R (`Module.Free R (MvPolynomial σ R)`)
2. Free ⟹ flat (`Module.Flat.of_free`)
3. Flat ⟹ going-down (`Algebra.HasGoingDown.of_flat`)
4. Going-down gives the height formula via
   `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
5. The prime P = I₁ + I₂ lies over I₁ in K[X₁]
6. P modulo I₁ has the same height as I₂ (base change by the domain K[X₁]/I₁)

The main difficulty is step 5–6: setting up the `LiesOver` instance and
computing the height of P modulo I₁ · K[X₁,X₂]. This requires MvPolynomial
variable-splitting plumbing that is nontrivial.

## Mathlib prerequisites (available)
- `Module.Free R (MvPolynomial σ R)` (`Mathlib.RingTheory.MvPolynomial.Basic`)
- `Module.Flat.of_free` (`Mathlib.RingTheory.Flat.Basic`)
- `Algebra.HasGoingDown.of_flat` (`Mathlib.RingTheory.Ideal.GoingDown`)
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
  (`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`)

## Mathlib gaps
- MvPolynomial variable-splitting: viewing `MvPolynomial (σ₁ ⊕ σ₂) R` as an
  algebra over `MvPolynomial σ₁ R` with `LiesOver` for split primes
- Height preservation under base change by a domain
-/

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial

/-- Heights add for prime ideals in disjoint variable sets in a polynomial ring.

Given σ = σ₁ ⊕ σ₂ and primes P₁ in K[X_{σ₁}], P₂ in K[X_{σ₂}], the prime
P = P₁ · K[X_σ] + P₂ · K[X_σ] has height = height(P₁) + height(P₂).

The inclusions use `MvPolynomial.rename Sum.inl` and `MvPolynomial.rename Sum.inr`. -/
theorem MvPolynomial.height_sup_disjoint
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    (I₁.map (MvPolynomial.rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom ⊔
     I₂.map (MvPolynomial.rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).height =
    I₁.height + I₂.height := by
  sorry

end
