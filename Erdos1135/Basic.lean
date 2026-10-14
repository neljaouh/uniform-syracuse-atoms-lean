import Mathlib.Tactic

/-!
# Basic Collatz Target Interfaces

This file contains the elementary Collatz step and proposition-level interfaces.
-/

open Function

namespace Erdos1135

/-- The standard Collatz step. -/
abbrev collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- The proposition hidden by the public `type_of%` wrapper in `Target.lean`. -/
def collatzProp : Prop :=
  ∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1

lemma collatzProp_def :
    collatzProp = (∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1) :=
  rfl

end Erdos1135
