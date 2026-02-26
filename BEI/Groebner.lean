import BEI.Definitions

-- We assume V is ordered (like Fin n).
variable {V : Type*} [LinearOrder V]

noncomputable section

def binomialEdgeLE (a b : BinomialEdgeVars V) : Prop :=
  match a, b with
  | Sum.inl u, Sum.inl v => u ≥ v -- Reversed order for x
  | Sum.inr u, Sum.inr v => u ≥ v -- Reversed order for y
  | Sum.inl _, Sum.inr _ => False -- x is never <= y
  | Sum.inr _, Sum.inl _ => True  -- y is always <= x

/--
The term order is lex on the variable order where
x > y and indices are descending 1 > 2 > ...
-/
@[reducible] instance : LinearOrder (BinomialEdgeVars V) where
  le := binomialEdgeLE
  toDecidableLE := Classical.decRel binomialEdgeLE

  -- Axioms
  le_refl a := by
    cases a <;> exact le_refl _

  le_trans a b c h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all only [binomialEdgeLE]
    -- Handle the two valid cases (x,x,x) and (y,y,y)
    · exact le_trans h2 h1
    · exact le_trans h2 h1

  le_antisymm a b h1 h2 := by
    -- Sum.inl.injEq / Sum.inr.injEq reduce the goal from `Sum.inl u = Sum.inl v` to `u = v`
    cases a <;> cases b <;> simp_all only [binomialEdgeLE, Sum.inl.injEq, Sum.inr.injEq]
    · exact le_antisymm h2 h1
    · exact le_antisymm h2 h1

  le_total a b := by
    cases a <;> cases b <;> simp only [binomialEdgeLE]
    case inl.inl => exact le_total _ _
    case inl.inr => exact Or.inr trivial
    case inr.inl => exact Or.inl trivial
    case inr.inr => exact le_total _ _

end

/-
-- Decidability
  -- Now we can point Classical.decRel to the specific function 'binomialEdgeLE'

  -- Need to check the axioms of a linear order
  -- Reflexivity
  le_refl a := by
    cases a <;> exact le_refl _

  -- Transitivity
  le_trans a b c h1 h2 := by
-- 1. Break down into the 8 combinations of x (inl) and y (inr)
    cases a <;> cases b <;> cases c

    -- 2. Force reduction of the 'match' statements in h1, h2, and the goal.
    --    This turns "match ... with ... => False" into actual "False".
    all_goals simp_all

    -- 3. Now handle the remaining logical states:

    -- Case: x <= x <= x (Transitivity of V, reversed)
    -- h1: v ≤ u, h2: w ≤ v ⊢ w ≤ u
    exact le_trans h2 h1

    -- Case: y <= y <= y (Transitivity of V, reversed)
    -- h1: v ≤ u, h2: w ≤ v ⊢ w ≤ u
    exact le_trans h2 h1

    -- Note: 'simp_all' automatically solves cases where h1 or h2 is False
    -- (contradiction) or where the goal is True.
    -- The only goals left after 'simp_all' are the two above.

  le_antisymm a b h1 h2 := by
  -- 1. Split into the 4 structural cases
    cases a <;> cases b

    -- 2. Handle the mixed cases (x vs y)
    -- In these cases, one of the hypotheses (h1 or h2) is effectively 'False'
    -- 'cases h1' or 'cases h2' will detect the False and close the goal immediately.
    case inl.inr => cases h1 -- x <= y is False
    case inr.inl => cases h2 -- y <= x means x <= y is False (via h2)

    -- 3. Handle the valid cases (x vs x, y vs y)
    -- We use 'all_goals' for the remaining 2 cases
    all_goals
      simp at * -- Reduces "Sum.inl u = Sum.inl v" to "u = v"
      -- Apply antisymmetry with SWAPPED arguments to account for the reversed order
      apply le_antisymm h2 h1

  le_total a b := by
    cases a <;> cases b
    -- 1. x vs x (inl, inl): Use linearity of V
    -- Logic: le_total u v -> (u >= v) or (v >= u) -> (x_u <= x_v) or (x_v <= x_u)
    case inl.inl => exact le_total _ _

    -- 2. y vs y (inr, inr): Use linearity of V
    case inr.inr => exact le_total _ _

    -- 3. x vs y (inl, inr):
    -- We need (x <= y) OR (y <= x). Since y <= x is True, the OR is True.
    case inl.inr => exact Or.inr True.intro

    -- 4. y vs x (inr, inl):
    -- We need (y <= x) OR (x <= y). Since y <= x is True, the first part is True.
    case inr.inl => exact Or.inl True.intro

  -- Decidability: We need to show that this is decidable
  toDecidableLE := Classical.decRel _ _
  -/
