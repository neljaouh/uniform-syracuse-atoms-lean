import PaperStatements
set_option backward.isDefEq.respectTransparency false

/-! Exact conversion between a finite fixed-total transport mass and the
number of contributing words. -/

namespace SyracuseReport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem density_depth_zero (r : ZMod (3 ^ 0)) : density 0 r = 2 / 3 := by
  have hr : r = 0 := by
    change (r : ZMod 1) = 0
    exact Subsingleton.elim (α := ZMod 1) r 0
  subst r
  simp [density, syracuseLaw]

theorem wordTransport_depth_zero (w : Word) (R : ℤ) :
    wordTransport w 0 R (density 0) =
      if Contributes w R then (2 / 3 : ℝ) * w.coefficient else 0 := by
  classical
  unfold wordTransport
  rw [density_depth_zero]
  split_ifs <;> ring

theorem fixed_total_contributing_mass (V : Finset Word) (R : ℤ) (d A : ℕ)
    (hstats : ∀ w ∈ V, w.length = d ∧ w.total = A)
    (hadmissible : ∀ w ∈ V, Contributes w R) :
    (∑ w ∈ V, wordTransport w 0 R (density 0)) =
      (V.card : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ d / (2 : ℝ) ^ A) := by
  classical
  calc
    (∑ w ∈ V, wordTransport w 0 R (density 0)) =
        ∑ _w ∈ V, ((2 / 3 : ℝ) * (3 : ℝ) ^ d / (2 : ℝ) ^ A) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [wordTransport_depth_zero, if_pos (hadmissible w hw)]
      simp only [Word.coefficient, (hstats w hw).1, (hstats w hw).2]
      ring
    _ = _ := by simp

theorem card_lower_of_fixed_total_transport (V : Finset Word) (R : ℤ) (d A : ℕ)
    (kappa : ℝ) (hstats : ∀ w ∈ V, w.length = d ∧ w.total = A)
    (hadmissible : ∀ w ∈ V, Contributes w R)
    (hmass : kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0)) :
    kappa * (3 / 2 : ℝ) * ((2 : ℝ) ^ A / (3 : ℝ) ^ d) ≤ (V.card : ℝ) := by
  rw [fixed_total_contributing_mass V R d A hstats hadmissible] at hmass
  have hscale : 0 < (2 / 3 : ℝ) * (3 : ℝ) ^ d / (2 : ℝ) ^ A := by positivity
  have hh : kappa / ((2 / 3 : ℝ) * (3 : ℝ) ^ d / (2 : ℝ) ^ A) ≤ (V.card : ℝ) :=
    (div_le_iff₀ hscale).mpr hmass
  convert hh using 1
  field_simp

end SyracuseReport
