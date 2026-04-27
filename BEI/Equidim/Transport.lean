import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import toMathlib.SquarefreeMonomialPrimes
import Mathlib.RingTheory.Regular.RegularSequence

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Equidimensional surrogate: regular elements, transport, and equidim transfer

This file isolates:

- regular elements `X(inl i) + X(inr i)` for the Cohen–Macaulay path
  (`sum_X_not_mem_minimalPrime`, `sum_XY_isSMulRegular`);
- the ideal-level transport from the monomial initial ideal to the bipartite
  edge monomial ideal via the y-predecessor shift
  (`rename_yPredVar_monomialInitialIdeal`);
- equidimensional surrogate transfer through ring isomorphisms
  (`isEquidim_of_ringEquiv`);
- the y-predecessor variable equivalence `yPredEquiv`;
- equidimensionality of the monomial initial ideal quotient under the
  Herzog–Hibi conditions (`monomialInitialIdeal_isEquidim`).

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

/-! ## Regular elements for the Cohen–Macaulay path

Under HH conditions, each linear form `X (Sum.inl i) + X (Sum.inr i)` avoids every
minimal prime of `bipartiteEdgeMonomialIdeal G`.  Since the edge ideal is radical
(proved via `variablePairIdeal_isRadical` in `SquarefreeMonomialPrimes`), these linear
forms are non-zero-divisors on the quotient ring — the first step toward showing the
quotient is Cohen–Macaulay via a direct regular-sequence argument. -/

/-- Under HH conditions, `X (Sum.inl i) + X (Sum.inr i)` is not in any minimal
prime of the bipartite edge monomial ideal.

Each minimal prime is `span (X '' C)` for a minimal vertex cover `C`, and
`minimalVertexCover_exactlyOne` ensures `C` picks exactly one element from
each diagonal pair `{Sum.inl i, Sum.inr i}`.  Therefore the other variable
is free in the quotient `S / P`, and the sum maps to a nonzero variable. -/
theorem sum_X_not_mem_minimalPrime {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G)) :
    X (Sum.inl i) + X (Sum.inr i) ∉ P := by
  -- Extract P = span(X '' C) for a minimal vertex cover C
  obtain ⟨C, hC, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  -- Under HH conditions, exactly one of Sum.inl i, Sum.inr i is in C
  have hexact := minimalVertexCover_exactlyOne hHH hC i hi
  -- Case split on which element of the diagonal pair is in C
  set S : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) := MvPolynomial.X '' C
  by_cases hxi : Sum.inl i ∈ C
  · -- Sum.inl i ∈ C, Sum.inr i ∉ C
    have hyi : Sum.inr i ∉ C := hexact.mp hxi
    intro hmem
    have hxi_mem : (X (Sum.inl i) : MvPolynomial _ K) ∈ Ideal.span S :=
      Ideal.subset_span ⟨Sum.inl i, hxi, rfl⟩
    have hyi_mem : (X (Sum.inr i) : MvPolynomial _ K) ∈ Ideal.span S := by
      have := (Ideal.span S).sub_mem hmem hxi_mem
      rwa [add_sub_cancel_left] at this
    exact hyi ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hyi_mem)
  · -- Sum.inl i ∉ C, Sum.inr i ∈ C
    have hyi : Sum.inr i ∈ C := by
      rcases hC.1 _ _ (hhEdgeSet_diagonal hHH i hi) with h | h
      · exact absurd h hxi
      · exact h
    intro hmem
    have hyi_mem : (X (Sum.inr i) : MvPolynomial _ K) ∈ Ideal.span S :=
      Ideal.subset_span ⟨Sum.inr i, hyi, rfl⟩
    have hxi_mem : (X (Sum.inl i) : MvPolynomial _ K) ∈ Ideal.span S := by
      have := (Ideal.span S).sub_mem hmem hyi_mem
      rwa [add_sub_cancel_right] at this
    exact hxi ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hxi_mem)

/-- The bipartite edge monomial ideal is radical, inherited from
`variablePairIdeal_isRadical` via the bridge
`bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`. -/
theorem bipartiteEdgeMonomialIdeal_isRadical {n : ℕ} (G : SimpleGraph (Fin n)) :
    (bipartiteEdgeMonomialIdeal (K := K) G).IsRadical := by
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  apply MvPolynomial.variablePairIdeal_isRadical
  intro a b hab
  obtain ⟨i, j, _, _, _, he⟩ := hab
  have := congr_arg Prod.fst he
  have := congr_arg Prod.snd he
  simp only [ne_eq] at *
  subst_vars
  exact Sum.inl_ne_inr

/-- Under HH conditions, `X (Sum.inl i) + X (Sum.inr i)` is a non-zero-divisor
on the quotient by the bipartite edge monomial ideal.

The proof uses three ingredients:
1. the edge ideal is radical (`bipartiteEdgeMonomialIdeal_isRadical`);
2. each minimal prime is a variable-generated prime from a minimal vertex cover;
3. the sum avoids every such prime (`sum_X_not_mem_minimalPrime`).

If `(x_i + y_i) · f ∈ I`, then `(x_i + y_i) · f ∈ P` for every minimal prime
`P` of `I`.  Since `P` is prime and `x_i + y_i ∉ P`, we get `f ∈ P`.  So
`f ∈ ⋂ P = radical(I) = I`. -/
theorem sum_XY_isSMulRegular {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl i) + X (Sum.inr i))) := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set ℓ : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inl i) + X (Sum.inr i)
  set mk := Ideal.Quotient.mk I
  intro a b hab
  -- Lift to the polynomial ring
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  -- Convert smul hypothesis to ring multiplication
  simp only [smul_eq_mul] at hab
  -- hab : mk ℓ * mk a' = mk ℓ * mk b'
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at hab
  -- hab : ℓ * a' - ℓ * b' ∈ I
  rw [Ideal.Quotient.eq]
  -- Goal: a' - b' ∈ I. Show it's in radical(I) = I.
  have hdiff : ℓ * (a' - b') ∈ I := by rwa [mul_sub]
  suffices a' - b' ∈ I.radical by
    rwa [(bipartiteEdgeMonomialIdeal_isRadical (K := K) G).radical] at this
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  intro P ⟨hPI, hPprime⟩
  -- Get a minimal prime Q of I with Q ≤ P
  haveI := hPprime
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hPI
  -- ℓ * (a' - b') ∈ I ⊆ Q (since Q is a minimal prime containing I)
  have hmemQ : ℓ * (a' - b') ∈ Q := hQmin.1.2 hdiff
  -- ℓ ∉ Q (our combinatorial result)
  have hℓ_not_Q := sum_X_not_mem_minimalPrime (K := K) hHH i hi hQmin
  -- Q is prime, so a' - b' ∈ Q
  have hab_Q := (hQmin.1.1.mem_or_mem hmemQ).resolve_left hℓ_not_Q
  -- Q ≤ P, so a' - b' ∈ P
  exact hQP hab_Q

/-! ## Ideal-level transport: monomial initial ideal → bipartite edge ideal -/

/-- The y-predecessor shift `φ` transports the monomial initial ideal to the bipartite
    edge monomial ideal: `φ(monomialInitialIdeal G) = bipartiteEdgeMonomialIdeal G`.

    This is the ideal-level packaging of the per-generator transport
    `rename_yPredVar_generator`, using `Ideal.map_span` to lift from generators to ideals.

    The key correspondences are:
    - Forward: edge `{i, j}` with `i < j` gives generator `x_i y_j`; after shift,
      `x_i y_{j-1}` with `{i, (j-1)+1} = {i, j} ∈ E(G)` and `i ≤ j-1`.
    - Backward: generator `x_i y_j` with `{i, j+1} ∈ E(G)` and `i ≤ j` lifts to
      `x_i y_{j+1}` with `{i, j+1} ∈ E(G)` and `i < j+1`. -/
theorem rename_yPredVar_monomialInitialIdeal {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    Ideal.map (rename (yPredVar n hn)) (monomialInitialIdeal (K := K) G) =
    bipartiteEdgeMonomialIdeal (K := K) G := by
  unfold monomialInitialIdeal bipartiteEdgeMonomialIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · -- Forward: each image of a monomialInitialIdeal generator is a bipartite generator
    apply Ideal.span_le.mpr
    rintro m ⟨f, ⟨i, j, hadj, hij, rfl⟩, rfl⟩
    apply Ideal.subset_span
    set j' : Fin n := ⟨j.val - 1, by omega⟩
    have hj'v : j'.val = j.val - 1 := rfl
    have hj'_succ : j'.val + 1 < n := by omega
    have hj'_adj : G.Adj i ⟨j'.val + 1, hj'_succ⟩ := by
      rw [show (⟨j'.val + 1, hj'_succ⟩ : Fin n) = j from
        Fin.ext (by dsimp only; omega)]
      exact hadj
    have hj'_le : i ≤ j' := by change i.val ≤ j'.val; omega
    exact ⟨i, j', hj'_succ, hj'_adj, hj'_le, rename_yPredVar_generator hn i j hij⟩
  · -- Backward: each bipartite generator is an image of a monomialInitialIdeal generator
    apply Ideal.span_le.mpr
    rintro m ⟨i, j, hj, hadj, hij, rfl⟩
    apply Ideal.subset_span
    set j' : Fin n := ⟨j.val + 1, by omega⟩
    have hj'v : j'.val = j.val + 1 := rfl
    have hij' : i < j' := by change i.val < j'.val; omega
    have hj'_eq : (⟨j'.val - 1, by omega⟩ : Fin n) = j :=
      Fin.ext (by dsimp only; omega)
    refine ⟨X (Sum.inl i) * X (Sum.inr j'), ⟨i, j', hadj, hij', rfl⟩, ?_⟩
    rw [rename_yPredVar_generator hn i j' hij', hj'_eq]

/-! ## Equidimensionality transfer through ring isomorphism -/

/-- The local equidimensional surrogate transfers across ring isomorphisms. -/
theorem isEquidim_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hEq : IsEquidimRing R) : IsEquidimRing S where
  equidimensional P Q hP hQ := by
    -- Pull back minimal primes of S to minimal primes of R
    have hP' : Ideal.comap e.toRingHom P ∈ minimalPrimes R := by
      have h := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom)
        e.surjective (I := ⊥) hP
      rwa [Ideal.comap_bot_of_injective e.toRingHom e.injective] at h
    have hQ' : Ideal.comap e.toRingHom Q ∈ minimalPrimes R := by
      have h := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom)
        e.surjective (I := ⊥) hQ
      rwa [Ideal.comap_bot_of_injective e.toRingHom e.injective] at h
    -- Quotient dimensions are preserved by the isomorphism
    have hPe : ringKrullDim (R ⧸ Ideal.comap e.toRingHom P) = ringKrullDim (S ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv _ P e
          (Ideal.map_comap_of_surjective e.toRingHom e.surjective P).symm)
    have hQe : ringKrullDim (R ⧸ Ideal.comap e.toRingHom Q) = ringKrullDim (S ⧸ Q) :=
      ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv _ Q e
          (Ideal.map_comap_of_surjective e.toRingHom e.surjective Q).symm)
    rw [← hPe, ← hQe]
    exact hEq.equidimensional _ _ hP' hQ'

/-! ## The y-predecessor variable equivalence -/

/-- The y-successor on BEI variables: inverse of `yPredVar`.
`x_i ↦ x_i`, `y_j ↦ y_{(j+1) mod n}`. -/
private def ySuccVar (n : ℕ) (hn : 0 < n) :
    BinomialEdgeVars (Fin n) → BinomialEdgeVars (Fin n)
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩

private lemma ySucc_yPred (n : ℕ) (hn : 0 < n) (v : BinomialEdgeVars (Fin n)) :
    ySuccVar n hn (yPredVar n hn v) = v := by
  cases v with
  | inl i => rfl
  | inr j =>
    simp only [yPredVar, ySuccVar]
    congr 1; ext; simp only
    have hj := j.isLt
    by_cases hj0 : j.val = 0
    · -- j = 0: pred = n-1, succ of that = n % n = 0
      rw [hj0, show 0 + n - 1 = n - 1 from by omega,
          Nat.mod_eq_of_lt (by omega : n - 1 < n),
          show (n - 1 + 1) = n from by omega, Nat.mod_self]
    · -- j > 0: pred = j-1, succ of that = j
      rw [show j.val + n - 1 = (j.val - 1) + 1 * n from by omega,
          Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : j.val - 1 < n),
          show j.val - 1 + 1 = j.val from by omega,
          Nat.mod_eq_of_lt hj]

private lemma yPred_ySucc (n : ℕ) (hn : 0 < n) (v : BinomialEdgeVars (Fin n)) :
    yPredVar n hn (ySuccVar n hn v) = v := by
  cases v with
  | inl i => rfl
  | inr j =>
    simp only [ySuccVar, yPredVar]
    congr 1; ext; simp only
    have hj := j.isLt
    by_cases hjn : j.val + 1 < n
    · -- j+1 < n: succ = j+1, pred of that = j
      rw [Nat.mod_eq_of_lt hjn]
      rw [show (j.val + 1 + n - 1) = j.val + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    · -- j = n-1: succ = 0, pred of that = n-1
      have hjeq : j.val = n - 1 := by omega
      rw [show j.val + 1 = n from by omega, Nat.mod_self]
      rw [show (0 + n - 1) = n - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
      exact hjeq.symm

/-- The y-predecessor shift as an equivalence on BEI variables.
`x_i ↦ x_i`, `y_j ↦ y_{(j-1) mod n}`, with inverse `y_j ↦ y_{(j+1) mod n}`. -/
def yPredEquiv (n : ℕ) (hn : 0 < n) :
    BinomialEdgeVars (Fin n) ≃ BinomialEdgeVars (Fin n) where
  toFun := yPredVar n hn
  invFun := ySuccVar n hn
  left_inv := ySucc_yPred n hn
  right_inv := yPred_ySucc n hn

/-! ## Equidimensionality of the monomial initial ideal quotient -/

/-- Under HH conditions, `S / monomialInitialIdeal G` is equidimensional in the
local surrogate sense.

Proof: the y-predecessor shift `φ` gives a ring isomorphism
`S / monomialInitialIdeal G ≃+* S / bipartiteEdgeMonomialIdeal G`,
and the bipartite edge ideal quotient is equidimensional by
`bipartiteEdgeMonomialIdeal_isEquidim`. -/
theorem monomialInitialIdeal_isEquidim {n : ℕ} (hn : 0 < n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsEquidimRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G) := by
  -- Build the ring equivalence from yPredEquiv
  set φ := (MvPolynomial.renameEquiv K (yPredEquiv n hn)).toRingEquiv
  -- Show φ maps monomialInitialIdeal to bipartiteEdgeMonomialIdeal
  have hmap : bipartiteEdgeMonomialIdeal (K := K) G =
      Ideal.map φ (monomialInitialIdeal (K := K) G) := by
    -- φ.toRingHom and rename (yPredVar n hn) act the same on generators
    have hfun : ⇑φ = ⇑(rename (yPredVar n hn) : MvPolynomial _ K →ₐ[K] MvPolynomial _ K) := by
      funext p; exact (MvPolynomial.renameEquiv_apply K (yPredEquiv n hn) p).symm
    change _ = Ideal.map φ.toRingHom _
    conv_rhs => rw [show φ.toRingHom = (rename (yPredVar n hn) :
        MvPolynomial _ K →ₐ[K] MvPolynomial _ K).toRingHom from RingHom.ext (fun x => by
      change φ x = rename (yPredVar n hn) x; exact congr_fun hfun x)]
    exact (rename_yPredVar_monomialInitialIdeal (K := K) hn G).symm
  -- Build the quotient isomorphism
  have e : MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G ≃+*
      MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.quotientEquiv _ _ φ hmap
  exact isEquidim_of_ringEquiv e.symm
    (bipartiteEdgeMonomialIdeal_isEquidim (K := K) hHH)

end
