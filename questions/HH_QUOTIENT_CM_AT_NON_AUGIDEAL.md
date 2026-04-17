# Cohen–Macaulayness of a Herzog–Hibi bipartite edge monomial ring

## Setup

Let `K` be a field, `n ≥ 2`, `σ := {x_0, …, x_{n-1}, y_0, …, y_{n-1}}` (so `|σ| = 2n`), and `S := K[σ]`. Fix a simple graph `G` on `{0, …, n-1}` satisfying the **Herzog–Hibi (HH) conditions**:

1. **Diagonal**: `{i, i+1} ∈ E(G)` for all `i < n−1`.
2. **Transitivity (Prop 1.6 condition)**: if `{i, j+1}, {j, k+1} ∈ E(G)` with `i < j < k`, then `{i, k+1} ∈ E(G)`.

Define the **HH bipartite edge monomial ideal**

```
I := ( x_i · y_j : i ≤ j,  j+1 < n,  {i, j+1} ∈ E(G) )  ⊂ S.
```

Let `R := S / I`. The associated bipartite graph `Γ` has vertex set `σ` and edge set

```
hhEdgeSet := { (x_i, y_j) : i ≤ j,  j+1 < n,  {i,j+1} ∈ E(G) }.
```

So `I` is the Stanley–Reisner (edge) ideal of `Γ`.

This setup arises in the proof of Proposition 1.6 of Herzog, Hibi, Hreinsdóttir, Kahle, Rauh, *Binomial edge ideals and conditional independence statements*, Adv. Appl. Math. **45** (2010), 317–333. The ideal `I` is the monomial initial ideal of a binomial edge ideal after a variable-shift automorphism.

## Already proved in our formalization (Lean)

- `dim R = n + 1`.
- `R` is **equidimensional**; `I` is radical (Stanley–Reisner).
- A specific regular sequence of length `n+1` in `R`:
  `fullRegSeq = [x_0 + y_0, x_1 + y_1, …, x_{n-2} + y_{n-2},  x_{n-1},  y_{n-1}]`.
- By flat base change this sequence is weakly regular on every localization `R_p`.
- Let `m⁺ := ker(S → K, x_i, y_i ↦ 0) / I` = augmentation (maximal) ideal.
- `R_{m⁺}` is Cohen–Macaulay (the `fullRegSeq` has length equal to `dim R_{m⁺} = n+1`).
- For any prime `p ⊆ m⁺`, `R_p ≅ (R_{m⁺})_{p'}` via localization-localization, so `R_p` is CM by CM-localizes.
- `MvPolynomial σ' K` is Cohen–Macaulay for any finite `σ'` (over any field `K`).

## The remaining gap

**Claim to prove.** `R` is Cohen–Macaulay, i.e., `R_p` is CM for every prime `p` of `R`.

The only open subcase is **`p ⊄ m⁺`**.

## What we've figured out and where natural approaches break

Let `Z := {v ∈ σ : \overline{v} ∈ p}` (non-unit vars in `R_p`) and `U := σ \ Z` (unit vars).
`Z` is a vertex cover of `hhEdgeSet` (primality). `p ⊄ m⁺` ⟺ `U ≠ ∅`.

For each `v ∈ Z` with a neighbor `w ∈ U` in `hhEdgeSet`, we get `\overline{v} · \overline{w} = 0` in `R` and `\overline{w}` a unit, so `\overline{v} = 0` in `R_p`. Call this set `Z_0 ⊆ Z`. Let `Z_1 := Z \ Z_0` (zero-variables with no unit neighbors).

**Naive hope** (and what an earlier internal guide asserts): `R_p` is a localization of a polynomial ring over `K` — i.e. all monomial relations vanish. This is **false in general**.

**Explicit counterexample.** Take `n = 4`, `G = K_4` (complete graph). Then

```
hhEdgeSet = {(x_0,y_0), (x_0,y_1), (x_1,y_1), (x_0,y_2), (x_1,y_2), (x_2,y_2)}.
```

Consider `p = (x_0, x_1, y_0, y_1, y_2, x_3 − 1) ⊂ R` (prime — quotient is `K[x_2, y_3]`, and `p ⊄ m⁺` since `x_3 − 1 ∉ m⁺`). Then:

- `U = {x_2, x_3, y_3}`; only `x_2` is edge-participating.
- `x_2` unit forces `y_2 = 0` in `R_p`.
- Surviving relations in `R_p`: `x_0·y_0 = x_0·y_1 = x_1·y_1 = 0`, with `x_0, x_1, y_0, y_1` all non-units.
- So `R_p` is isomorphic to *(the n=3 triangle HH ring localized at its augmentation ideal)* ⊗_K *(K[x_2, x_3, y_3] localized at `(x_3 − 1)`)*, and this still has live monomial relations.

So for this `p`, `R_p` is not a polynomial ring localization; it is a **nontrivial tensor product of a smaller HH-at-augmentation ring with a polynomial ring localization**.

## Questions

**Q1 (strategy).** What is the cleanest / most formalization-friendly mathematical proof that `R_p` is Cohen–Macaulay for every prime `p` of `R`?

We are looking for an approach that
(a) does not require Hochster's full simplicial-complex CM characterization (which is substantial to formalize);
(b) can plausibly use the inputs we already have — `fullRegSeq` weakly regular on `R_p`, polynomial-CM, CM-localizes, CM transfer through `RingEquiv`, the graded contraction lemma "invertible constant coefficient ⟹ NZD" in `MvPolynomial σ K / I` for monomial `I`.

**Q2 (structural decomposition).** Is it correct that for any prime `p ⊄ m⁺`, `R_p` is naturally of the form

```
(HH-at-augmentation ring for a smaller HH graph)  ⊗_K  (polynomial ring in free variables) , localized at some prime
```

— and if so, what is the precise statement and proof? We would like an explicit ring decomposition or isomorphism we can target in Lean.

**Q3 (regular sequence).** The `fullRegSeq` of length `n+1` is weakly regular on `R_p`. In the `p ⊄ m⁺` case, some entries become units in `R_p`. Is there a clean argument that the sub-sequence of entries landing in `p · R_p` has length equal to `primeHeight(p) = dim R_p`? If so, this directly gives CM via `length = dim`. The dimension side is the non-obvious one — how do we compute `primeHeight(p)` cleanly?

**Q4 (alternative: direct parameter system).** For the counterexample `p ⊄ m⁺` above, can you write down an explicit system of parameters in `p · R_p` of length `dim R_p` together with the weakly-regular verification? A general recipe (not just the example) would be ideal.

**Q5 (alternative: Gröbner / edge-ideal route).** Is there a standard CM criterion for edge ideals of bipartite graphs satisfying Herzog–Hibi conditions that avoids checking every localization — e.g., a global criterion using the full regular sequence plus unmixedness, or a reduction to a shellability / matroidal argument that is elementary enough to formalize?

**Q6 (tensor / base-change CM).** If the right picture is `R_p ≅ A ⊗_K K[σ''] ` (localized), we would need: `A` CM local + polynomial base change + further localization ⟹ CM. Is there a clean statement of the form "CM local ring ⊗_K polynomial ring, localized at a prime, is CM" that we can target as the key lemma?

Please give the precise mathematical statement(s) that should be formalized and a sketch of the proof, keeping in mind we want the smallest infrastructure that closes the gap rather than a full Stanley–Reisner / depth-theoretic framework.
