import BEI.Definitions

-- We assume V is ordered (like Fin n).
variable {V : Type*} [LinearOrder V]

noncomputable section

/--
The ordering on `BinomialEdgeVars V` for the Gröbner basis term order.
Under this ordering: `y < x` (all y-variables precede all x-variables),
and within each block, indices are descending (`x_n > ... > x_1`, `y_n > ... > y_1`).
-/
@[reducible] def binomialEdgeLE (a b : BinomialEdgeVars V) : Prop :=
  match a, b with
  | Sum.inl u, Sum.inl v => u ≥ v -- Reversed order for x
  | Sum.inr u, Sum.inr v => u ≥ v -- Reversed order for y
  | Sum.inl _, Sum.inr _ => False -- x is never <= y
  | Sum.inr _, Sum.inl _ => True  -- y is always <= x

/--
The term order is lex on the variable order where
x > y and indices are descending: x_n > ... > x_1 > y_n > ... > y_1
-/
noncomputable instance : LinearOrder (BinomialEdgeVars V) where
  le := binomialEdgeLE
  lt := fun a b => binomialEdgeLE a b ∧ ¬binomialEdgeLE b a
  toDecidableLE := Classical.decRel binomialEdgeLE

  le_refl a := by
    cases a <;> exact le_refl _

  le_trans a b c h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all only [binomialEdgeLE]
    · exact le_trans h2 h1
    · exact le_trans h2 h1

  le_antisymm a b h1 h2 := by
    cases a <;> cases b <;> simp_all only [binomialEdgeLE]
    · exact congrArg Sum.inl (le_antisymm h2 h1)
    · exact congrArg Sum.inr (le_antisymm h2 h1)

  le_total a b := by
    cases a <;> cases b <;> simp only [binomialEdgeLE]
    case inl.inl => exact le_total _ _
    case inl.inr => exact Or.inr trivial
    case inr.inl => exact Or.inl trivial
    case inr.inr => exact le_total _ _

end
