import ResearchWeightedCauchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.PNat.Equiv

/-! One-letter tilted weights for the quadratic cylinder-energy argument. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def tiltedLetterWeight (a : ℕ+) : ℝ :=
  3 / (4 : ℝ) ^ (a : ℕ)

theorem tiltedLetterWeight_pos (a : ℕ+) : 0 < tiltedLetterWeight a := by
  unfold tiltedLetterWeight
  positivity

theorem shifted_square_geometric_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * r ^ n) := by
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hr)
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h : Summable (fun n : ℕ =>
      (n : ℝ) ^ 2 * r ^ n + 2 * ((n : ℝ) * r ^ n) + r ^ n) :=
    (h2.add (h1.mul_left 2)).add h0
  apply h.congr
  intro n
  push_cast
  ring

theorem tiltedLetterWeight_summable : Summable tiltedLetterWeight := by
  let r : ℝ := 1 / 4
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hnat : Summable (fun n : ℕ => (3 / 4 : ℝ) * r ^ n) :=
    (summable_geometric_of_norm_lt_one hr).mul_left (3 / 4)
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  convert hnat using 1
  funext n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
    Nat.succPNat_coe]
  dsimp [tiltedLetterWeight, r]
  rw [pow_succ]
  rw [one_div_pow]
  field_simp

theorem tiltedLetterWeight_total : (∑' a : ℕ+, tiltedLetterWeight a) = 1 := by
  let r : ℝ := 1 / 4
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hgeom : (∑' n : ℕ, r ^ n) = 1 / (1 - r) := by
    simpa only [one_div] using tsum_geometric_of_norm_lt_one hr
  calc
    (∑' a : ℕ+, tiltedLetterWeight a) =
        ∑' n : ℕ, tiltedLetterWeight (Equiv.pnatEquivNat.symm n) :=
      (Equiv.pnatEquivNat.symm.tsum_eq tiltedLetterWeight).symm
    _ = ∑' n : ℕ, (3 / 4 : ℝ) * r ^ n := by
      apply tsum_congr
      intro n
      simp only [Equiv.pnatEquivNat_symm_apply]
      dsimp [tiltedLetterWeight, r]
      rw [pow_succ, one_div_pow]
      field_simp
    _ = (3 / 4 : ℝ) * ∑' n : ℕ, r ^ n := by rw [tsum_mul_left]
    _ = 1 := by rw [hgeom]; norm_num [r]


theorem tiltedLetterWeight_secondMoment_summable :
    Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ 2 * tiltedLetterWeight a) := by
  let r : ℝ := 1 / 4
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hnat : Summable (fun n : ℕ =>
      (3 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 * r ^ n)) :=
    (shifted_square_geometric_summable r hr).mul_left (3 / 4)
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  convert hnat using 1
  funext n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
    Nat.succPNat_coe]
  dsimp [tiltedLetterWeight, r]
  rw [pow_succ]
  rw [one_div_pow]
  field_simp
  simp [pow_succ]
  ring

theorem tiltedLetterWeight_firstMoment_summable :
    Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) * tiltedLetterWeight a) := by
  apply Summable.of_nonneg_of_le
  · intro a
    exact mul_nonneg (by positivity) (tiltedLetterWeight_pos a).le
  · intro a
    have ha : (1 : ℝ) ≤ (a : ℕ) := by exact_mod_cast a.pos
    have ha2 : ((a : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right ha2 (tiltedLetterWeight_pos a).le
  · exact tiltedLetterWeight_secondMoment_summable

theorem geometricLetter_secondMoment_summable :
    Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ 2 *
      (1 / (2 : ℝ) ^ (a : ℕ))) := by
  let r : ℝ := 1 / 2
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hnat : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 * r ^ n)) :=
    (shifted_square_geometric_summable r hr).mul_left (1 / 2)
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  convert hnat using 1
  funext n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
    Nat.succPNat_coe]
  dsimp [r]
  rw [pow_succ]
  rw [one_div_pow]
  field_simp
  simp [pow_succ]
  ring

end SyracuseReport
