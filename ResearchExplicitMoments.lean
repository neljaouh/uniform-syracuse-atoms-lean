import ResearchMixedSecond
import Mathlib.Data.Nat.Choose.Cast

/-! Exact evaluation of the ordinary and tilted one-letter moments. -/
namespace SyracuseReport
open scoped BigOperators

theorem hasSum_shifted_first_geometric (r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hr

theorem hasSum_shifted_second_geometric (r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r ^ n)
      (2 / (1 - r) ^ 3 - 1 / (1 - r) ^ 2) := by
  have h := ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left 2).sub
    (hasSum_shifted_first_geometric r hr)
  convert h using 1
  · funext n
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
    ring
  · ring

theorem tiltedFirstMoment_exact : tiltedFirstMoment = 4 / 3 := by
  unfold tiltedFirstMoment
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  have h := (hasSum_shifted_first_geometric (1 / 4) (by norm_num)).mul_left (3 / 4)
  have heq : (fun n : ℕ =>
      ((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) *
        tiltedLetterWeight (Equiv.pnatEquivNat.symm n)) =
      (fun n : ℕ => (3 / 4 : ℝ) * (((n : ℝ) + 1) * (1 / 4 : ℝ) ^ n)) := by
    funext n
    simp only [Equiv.pnatEquivNat_symm_apply]
    dsimp [tiltedLetterWeight]
    push_cast
    rw [pow_succ, one_div_pow]
    field_simp <;> simp [pow_succ, mul_comm]
  rw [heq, h.tsum_eq]
  norm_num

theorem tiltedSecondMoment_exact : tiltedSecondMoment = 20 / 9 := by
  unfold tiltedSecondMoment
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  have h := (hasSum_shifted_second_geometric (1 / 4) (by norm_num)).mul_left (3 / 4)
  have heq : (fun n : ℕ =>
      (((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) : ℝ) ^ 2 *
        tiltedLetterWeight (Equiv.pnatEquivNat.symm n)) =
      (fun n : ℕ => (3 / 4 : ℝ) * (((n : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ n)) := by
    funext n
    simp only [Equiv.pnatEquivNat_symm_apply]
    dsimp [tiltedLetterWeight]
    push_cast
    rw [pow_succ, one_div_pow]
    field_simp <;> simp [pow_succ, mul_comm]
  rw [heq, h.tsum_eq]
  norm_num

theorem geometricFirstMoment_exact : geometricFirstMoment = 2 := by
  unfold geometricFirstMoment
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  have h := (hasSum_shifted_first_geometric (1 / 2) (by norm_num)).mul_left (1 / 2)
  have heq : (fun n : ℕ =>
      ((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) *
        geometricLetterWeight (Equiv.pnatEquivNat.symm n)) =
      (fun n : ℕ => (1 / 2 : ℝ) * (((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n)) := by
    funext n
    simp only [Equiv.pnatEquivNat_symm_apply, geometricLetterWeight,
      Word.probability, oneLetterWord_total]
    dsimp
    push_cast
    rw [pow_succ, one_div_pow]
    field_simp <;> simp [pow_succ, mul_comm]
  rw [heq, h.tsum_eq]
  norm_num

theorem geometricSecondMoment_exact : geometricSecondMoment = 6 := by
  unfold geometricSecondMoment
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  have h := (hasSum_shifted_second_geometric (1 / 2) (by norm_num)).mul_left (1 / 2)
  have heq : (fun n : ℕ =>
      (((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) : ℝ) ^ 2 *
        geometricLetterWeight (Equiv.pnatEquivNat.symm n)) =
      (fun n : ℕ => (1 / 2 : ℝ) * (((n : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ n)) := by
    funext n
    simp only [Equiv.pnatEquivNat_symm_apply, geometricLetterWeight,
      Word.probability, oneLetterWord_total]
    dsimp
    push_cast
    rw [pow_succ, one_div_pow]
    field_simp <;> simp [pow_succ, mul_comm]
  rw [heq, h.tsum_eq]
  norm_num

end SyracuseReport
