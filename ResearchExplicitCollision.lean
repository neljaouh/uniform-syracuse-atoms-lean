import ResearchCollisionUpper
import ResearchExplicitMoments
import DensityRegularity

/-! Explicit polynomial constants in the collision-energy upper bound. -/
namespace SyracuseReport
open MeasureTheory
open scoped BigOperators

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem tiltedTotalSecondMomentFormula_exact (n : ℕ) :
    tiltedTotalSecondMomentFormula n =
      (16 / 9 : ℝ) * (n : ℝ) ^ 2 + (4 / 9 : ℝ) * n := by
  unfold tiltedTotalSecondMomentFormula
  rw [tiltedFirstMoment_exact, tiltedSecondMoment_exact]
  ring

theorem tiltedOffsetSecondMomentFormula_exact (n : ℕ) :
    tiltedOffsetSecondMomentFormula n =
      (76 / 81 : ℝ) * (n : ℝ) ^ 3 + (1 / 27 : ℝ) * (n : ℝ) ^ 2 -
        (19 / 81 : ℝ) * n := by
  rw [tiltedOffsetSecondMomentFormula_eq_cubic]
  unfold tiltedOffsetSecondMomentCubic
  rw [tiltedFirstMoment_exact, tiltedSecondMoment_exact,
    geometricFirstMoment_exact, geometricSecondMoment_exact]
  ring

/-- An explicit polynomial bound for every positive depth. -/
theorem collisionEnergy_explicit_upper (n : ℕ) (hn : 1 ≤ n) :
    collisionEnergy n ≤
      (608 / 243 : ℝ) * (n : ℝ) ^ 2 + (392 / 81 : ℝ) * n + 136 / 243 := by
  have h := mul_le_mul_of_nonneg_left (actual_collision_moment_bound n hn)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [tiltedTotalSecondMomentFormula_exact, tiltedOffsetSecondMomentFormula_exact] at h
  convert h using 1
  · unfold collisionEnergy
    ring
  · field_simp
    <;> ring

theorem collisionEnergy_le_eight_sq (n : ℕ) (hn : 1 ≤ n) :
    collisionEnergy n ≤ 8 * (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h := collisionEnergy_explicit_upper n hn
  nlinarith

/-- The finite-density L2 bound in the unit-Haar normalization. -/
theorem integral_density_sq_le_eight_sq (n : ℕ) (hn : 1 ≤ n) :
    (∫ x, (cylinderFunction n (density n) x) ^ 2 ∂unitHaar) ≤
      8 * (n : ℝ) ^ 2 := by
  rw [integral_density_sq n hn]
  exact collisionEnergy_le_eight_sq n hn

end SyracuseReport
