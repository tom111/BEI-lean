import BEI

/-!
# Axiom regression check

Build-time `#guard_msgs` assertions for the paper-facing flagship theorems.
If any of these starts depending on a new axiom (typically `sorryAx` if a
`sorry` slipped in, or some import dragging in `Quot.lift` / `Classical.choice`
flavours we did not previously rely on), the build fails *here* rather than
silently in some downstream consumer.

Each block asserts that the named theorem depends on exactly
`[propext, Classical.choice, Quot.sound]` — the standard Lean foundation
axioms used by Mathlib classical reasoning. Any deviation (extra axiom
appearing or any of the three disappearing) breaks the build.

To regenerate the expected message after an intentional axiom change, run
`#print axioms <name>` in a scratch file and copy the output verbatim into
the docstring above the corresponding `#guard_msgs in #print axioms` line.

This file is built as part of the default Lake target via the `BEI`
library glob.
-/

namespace BEI.AxiomCheck

-- Section 2 ------------------------------------------------------------------

/-- info: 'theorem_2_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theorem_2_1

/-- info: 'corollary_2_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corollary_2_2

/-- info: 'MonomialOrder.isGroebnerBasis_iff_sPolynomial_isRemainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonomialOrder.isGroebnerBasis_iff_sPolynomial_isRemainder

-- Section 1 / Theorem 1.1 ----------------------------------------------------

/-- info: 'closed_implies_groebner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_implies_groebner

/-- info: 'groebner_implies_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms groebner_implies_closed

/-- info: 'proposition_1_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proposition_1_6

-- Section 3 ------------------------------------------------------------------

/-- info: 'theorem_3_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theorem_3_2

/-- info: 'corollary_3_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corollary_3_3

/-- info: 'corollary_3_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corollary_3_4

/-- info: 'corollary_3_7_cm_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corollary_3_7_cm_fin

-- Equidim / monomial-initial flagship ---------------------------------------

/-- info: 'monomialInitialIdeal_isCohenMacaulay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms monomialInitialIdeal_isCohenMacaulay

end BEI.AxiomCheck
