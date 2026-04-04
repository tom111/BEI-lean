# Answer to Q12: `iSup` Cast Lemma and `cycle_induce_preconnected`

## Preserved question

This question has two separate Lean issues.

### Problem A

In `BEI/PrimeDecomposition.lean`, after the mathematical proof of `corollary_3_3`,
there remains a cast-through-`iSup` goal of the form

```lean
⊢ ⨆ S, ↑(Fintype.card V - S.card + componentCount G S) =
    ↑(⨆ S, Fintype.card V - S.card + componentCount G S)
```

where the left-hand `iSup` lives in `WithBot ℕ∞` and the right-hand side is the cast of
the `ℕ`-valued supremum.

### Problem B

In `BEI/MinimalPrimes.lean`, one still needs

```lean
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    (G.induce {x : V | x ∉ ({v} : Finset V)}).Preconnected
```

The question asked for a complete Lean 4 proof, especially for Problem B.


## Problem A: cast through `iSup`

## Short answer

Use a maximizing witness for the finite `ℕ`-valued function. Do not search for a special
cast-through-`iSup` theorem first.

## Recommended route

Let

```lean
f : Finset V → ℕ := fun S => Fintype.card V - S.card + componentCount G S
```

Because `Finset V` is a finite type, obtain:

```lean
obtain ⟨S₀, hmax⟩ : ∃ S₀, ∀ S, f S ≤ f S₀ := ...
```

Then prove:

```lean
have hsup_nat : (⨆ S, f S) = f S₀ := by
  apply le_antisymm
  · exact iSup_le hmax
  · exact le_iSup f S₀
```

and for the `WithBot ℕ∞`-side:

```lean
have hS0 : (↑(f S₀) : WithBot ℕ∞) ≤ ⨆ S, (↑(f S) : WithBot ℕ∞) := by
  exact le_iSup (fun S => (↑(f S) : WithBot ℕ∞)) S₀
```

This gives the hard direction immediately after rewriting by `hsup_nat`.

## Practical point

Even if a general lemma exists, the witness-based proof is likely shorter and more stable
in this concrete setting.


## Problem B: `cycle_induce_preconnected`

## Short answer

The shortest-walk strategy from Answer 10 is still the right one.
The newer path-splicing idea in the question is not actually simpler, because it becomes
circular when it tries to use reachability of `n2` to `n1` in the induced graph.

## Recommended worker task

For fixed `t ∈ S`, do:

1. choose a shortest walk `p : G.Walk t n1` with `p.length = G.dist t n1`;
2. prove `v ∉ p.support`;
3. transfer `p` to the induced graph `G.induce S`;
4. conclude `Reachable ⟨t, ht⟩ ⟨n1, hn1S⟩`.

## Key helper

The real missing lemma is:

```lean
private lemma shortest_walk_to_n1_avoids_v
    (p : G.Walk t n1) (hp : p.length = G.dist t n1)
    (htv : t ≠ v) (hn1v : n1 ≠ v) :
    v ∉ p.support
```

This should be proved by contradiction using local analysis around the occurrence of `v`
in a shortest walk:

- `v` is an internal vertex of the support;
- predecessor and successor are neighbors of `v`;
- `v` has exactly two neighbors `n1` and `n2`;
- each possible local configuration shortens the walk.

## What not to do

- do not use the parity argument from the old comment;
- do not attempt a global reroute through `n2`;
- do not reason directly with `componentCount` here.


## Final recommendation

### For Problem A

Solve the cast goal by finite maximization.

### For Problem B

Stick with the shortest-walk-avoids-`v` route from Answer 10. That remains the most
direct non-circular path.
