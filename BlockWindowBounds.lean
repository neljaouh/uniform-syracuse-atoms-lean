import BlockFamilies
import Mathlib.Algebra.Order.Floor.Semifield

/-! Bounds for the actual ceiling window in the fixed-block construction. -/

namespace SyracuseReport

theorem blockLength_real_ge_one (j : ℕ) : (1 : ℝ) ≤ blockLength j := by
  have h := blockLength_ge_200 j
  exact_mod_cast (show 1 ≤ blockLength j by omega)

theorem blockWindow_real_ge_rpow (j : ℕ) :
    (blockLength j : ℝ) ^ (3 / 5 : ℝ) ≤ (blockWindow j : ℝ) := by
  exact Nat.le_ceil _

theorem blockWindow_real_le_two_rpow (j : ℕ) :
    (blockWindow j : ℝ) ≤ 2 * (blockLength j : ℝ) ^ (3 / 5 : ℝ) := by
  apply Nat.ceil_le_two_mul
  have h := Real.one_le_rpow (blockLength_real_ge_one j)
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  linarith

theorem blockLength_rpow_two_fifths_ge_twenty_five (j : ℕ) :
    (25 : ℝ) ≤ (blockLength j : ℝ) ^ (2 / 5 : ℝ) := by
  have hb : (5 : ℝ) ^ 5 ≤ blockLength j := by
    have h := baseBlockLength_le j
    norm_num [baseBlockLength] at h
    exact_mod_cast (show 3125 ≤ blockLength j by omega)
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (5 : ℝ) ^ 5)
    hb (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have heq : ((5 : ℝ) ^ 5) ^ (2 / 5 : ℝ) = 25 := by
    rw [← Real.rpow_natCast (5 : ℝ) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  rwa [heq] at hpow

theorem blockWindow_real_le_tenth (j : ℕ) :
    (blockWindow j : ℝ) ≤ (blockLength j : ℝ) / 10 := by
  have hwin := blockWindow_real_le_two_rpow j
  have hb : (0 : ℝ) < blockLength j :=
    lt_of_lt_of_le (by norm_num) (blockLength_real_ge_one j)
  have hlarge := blockLength_rpow_two_fifths_ge_twenty_five j
  have hnonneg : 0 ≤ (blockLength j : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have hprod : (blockLength j : ℝ) ^ (3 / 5 : ℝ) *
      (blockLength j : ℝ) ^ (2 / 5 : ℝ) = blockLength j := by
    rw [← Real.rpow_add hb]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_left hlarge hnonneg]

theorem blockWindow_pos (j : ℕ) : 0 < blockWindow j := by
  have hr := Real.one_le_rpow (blockLength_real_ge_one j)
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hw := blockWindow_real_ge_rpow j
  have : (0 : ℝ) < blockWindow j := by linarith
  exact_mod_cast this

end SyracuseReport
