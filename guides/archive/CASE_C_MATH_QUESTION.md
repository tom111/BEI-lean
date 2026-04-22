# Prompt for deep-thinking math model: closing Case C of graded local-to-global CM

## Goal

Close the non-homogeneous-prime branch of the graded local-to-global Cohen-Macaulay theorem (Bruns-Herzog 2.1.27).

**Precise statement to prove**:
Let `A` be a connected ℕ-graded Noetherian commutative ring over a field `K` (`𝒜₀ = K`, so connected). Let `𝒜₊` be the irrelevant ideal. Assume `A_{𝒜₊}` is Cohen-Macaulay local. Then `A_p` is Cohen-Macaulay local for **every** prime `p ⊂ A` — including non-homogeneous primes.

## Building blocks already available

1. **CM-localizes**: `B_𝔪` CM + `p ⊆ 𝔪` ⟹ `B_p` CM. Covers any prime `p ⊆ 𝒜₊`, homogeneous or not.
2. **BH 1.5.6 / Eisenbud 3.5** (just proved in Lean): every `q ∈ Ass(A)` is a homogeneous ideal. Hence `Ass(A) ⊆ 𝒜₊`.
3. **Graded prime avoidance**: a homogeneous NZD `ℓ ∈ 𝒜₊` exists whenever no `q ∈ Ass(A)` contains `𝒜₊`.
4. **NZD descent `ℓ ∈ p`**: if `ℓ` is NZD on `B`, `ℓ ∈ p`, and `(B/⟨ℓ⟩)_{p/⟨ℓ⟩}` is CM, then `B_p` is CM.

The easy side (`p ⊆ 𝒜₊`) is fully handled by (1). The problem is **primes `p ⊄ 𝒜₊`**.

## The obstacle

Standard plan (Option 1a of the BEI project's `ROUTE_B_OBSTACLE_PLAN.md`): induct on `height(p)`. Since `Ass(A) ⊆ 𝒜₊` and `p ⊄ 𝒜₊`, we have `p ⊄ q` for every `q ∈ Ass(A)`, so `p` contains a non-zero-divisor `ℓ'` (classical prime avoidance). Apply (4) to reduce to `B := A/⟨ℓ'⟩` and `p' := p/⟨ℓ'⟩`. Recurse.

**Obstacle 1** — the NZD `ℓ'` is necessarily **non-homogeneous**: homogeneous elements of a proper ideal `p ⊄ 𝒜₊` all lie in `𝒜₊` (the degree-0 part would be a unit in `K^*`, forcing `p = ⊤`). So `B = A/⟨ℓ'⟩` is *not* naturally graded.

**Obstacle 2** — even if we pick `ℓ' ∈ p ∩ 𝒜₊` NZD (which exists when `p ∩ 𝒜₊` avoids `Ass(A)`), the induction invariant breaks:
   - "`B_𝔪'` CM" where `𝔪' = 𝒜₊/⟨ℓ'⟩`: OK, descends via (4) applied to the pair `(ℓ', 𝒜₊)`.
   - "`Ass(B) ⊆ 𝔪'`": **fails in general**. A prime `q ⊂ A` containing `ℓ'` (so `q/⟨ℓ'⟩ ∈ Ass(B)`) need not be `⊆ 𝒜₊`. Example: `A = K[x,y,z]`, `ℓ' = x`, then `q = (x, y-1) ⊄ (x,y,z)`.

**Obstacle 3** — if we instead allow `ℓ' ∉ 𝒜₊`, then `𝒜₊ + ⟨ℓ'⟩ = A` (since `𝒜₊` is maximal), so the image of `𝒜₊` in `B` is `⊤`, and `B_𝔪'` is meaningless.

## The question

What is the correct mathematical strategy?

Three candidates we can think of:

**(a) A better induction invariant.** Is there a predicate `P(B, 𝔪)` on `(Noetherian ring, maximal ideal)` such that:
   - `P(A, 𝒜₊)` holds given our hypotheses;
   - `P(B, 𝔪)` implies `B_p` is CM for every prime `p`;
   - `P` is *preserved* under quotient by any NZD `ℓ ∈ 𝔪`, with `𝔪` replaced by `𝔪/⟨ℓ⟩`?

   Classical candidates for `P`:
   - "`B_𝔪` CM + `Ass(B) ⊆ 𝔪`" — fails, see Obstacle 2.
   - "`B_𝔪` CM + `B` has a *unique* associated prime inside `𝔪`" — does this propagate?
   - "`B` is CM as a ring at `𝔪` *and* at every localization" — circular.
   - Something involving unmixedness of every quotient by a system of parameters?

**(b) An algebraic identity avoiding recursion.** Can we directly express `depth(A_p)` or `dim(A_p)` in terms of invariants of `A_{p*}` where `p* = p.homogeneousCore 𝒜`, without routing through *-depth? BH 1.5.8 gives the formula

   `depth(A_p) + dim(A_p / p·A_p) = depth(A_{p*}) + dim(A_{p*} / p*·A_{p*})`

   Is there a simpler argument giving `depth(A_p) ≥ depth(A_{p*})` that doesn't need the full *-depth/dim framework?

**(c) *-depth / Route A in full generality.** If this is genuinely the only route, what is the *minimum* infrastructure needed? Specifically:
   - Does the full BH 1.5.8 (depth/dim identity) actually require *-depth theory, or can it be proved using only ordinary depth plus graded Noether normalization?
   - Can we bypass BH 1.5.8 with a finite-extension CM transfer from a Noether normalization `K[θ_1, …, θ_d] ↪ A`?

**(d) BEI-specific escape hatch.** Our downstream consumer is `A = S[t]/Ĩ` where `Ĩ` is the Gröbner deformation ideal (`S = K[x_1, …, x_n, y_1, …, y_n]`, `Ĩ = (f̃_{i,j})`, BEI paper by Herzog-Hibi-Hreinsdóttir-Kahle-Rauh 2010). Is there any *structural* feature of this specific ring — flatness over `K[t]`, the specific form of the `f̃_{i,j}`, properties of the fiber `A/⟨t-1⟩ = S/J_G` for closed graphs `G` — that lets us prove `A` globally CM *without* going through the general graded LTG theorem?

## What I need back

For whichever route is most tractable:
1. The exact invariant / induction variable / identity.
2. A proof sketch in precise algebraic terms (citable lemmas, not prose).
3. The list of "missing" commutative-algebra facts that would need to be formalized (we have standard Noetherian, height, Krull dimension, depth, regular sequences, and localization theory in Mathlib/toMathlib; we do *not* yet have *-depth, graded Noether normalization, graded finite-extension CM transfer, or Conca-Varbaro-style monomial/initial-ideal CM transfer).

If the cleanest route is (d) — a BEI-specific argument — that's the most valuable answer, since it would let us bypass the general theorem entirely.
