import Erdos1135.Tao.Probability.Geom2CenteredMoment

/-! Quadratic exponential moments with the constant used by the fixed-block
acceptance estimate. -/

namespace SyracuseReport
open Erdos1135.Tao

theorem exp_sub_one_abs_le_four_thirds {t : ℝ} (ht : |t| ≤ 1 / 4) :
    |Real.exp t - 1| ≤ (4 / 3 : ℝ) * |t| := by
  by_cases ht0 : 0 ≤ t
  · have htq : t ≤ 1 / 4 := (le_abs_self t).trans ht
    have ht1 : t < 1 := by linarith
    have hexp := Real.exp_bound_div_one_sub_of_interval ht0 ht1
    have hden : 0 < 1 - t := by linarith
    have hbound : (1 - t)⁻¹ ≤ 1 + (4 / 3 : ℝ) * t := by
      apply (inv_le_iff_one_le_mul₀ hden).2
      nlinarith [mul_nonneg ht0 (show 0 ≤ 1 - 4 * t by linarith)]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht0)),
      abs_of_nonneg ht0]
    have hexp' : Real.exp t ≤ (1 - t)⁻¹ := by simpa [one_div] using hexp
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hlin := Real.add_one_le_exp t
    rw [abs_of_neg (sub_neg.mpr (Real.exp_lt_one_iff.mpr htneg)),
      abs_of_neg htneg]
    linarith

theorem centeredMoment_le_exp_three_sq {t : ℝ} (ht : |t| ≤ 1 / 4) :
    taoGeom2CenteredExpMoment t ≤ Real.exp (3 * t ^ 2) := by
  let u := Real.exp t - 1
  have hu : |u| ≤ (4 / 3 : ℝ) * |t| := exp_sub_one_abs_le_four_thirds ht
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hu2 : u ^ 2 ≤ (16 / 9 : ℝ) * t ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg u) hu 2
    nlinarith [sq_abs u, sq_abs t]
  have huSmall : u ^ 2 ≤ 1 / 9 := by nlinarith
  have hadm : Real.exp t < 2 := by
    have habs := le_abs_self u
    have htq := ht
    dsimp [u] at habs hu
    linarith
  have hden : 0 < 1 - u ^ 2 := by nlinarith [sq_nonneg u]
  have hinv : (1 - u ^ 2)⁻¹ ≤ 1 + (9 / 8 : ℝ) * u ^ 2 := by
    apply (inv_le_iff_one_le_mul₀ hden).2
    have hprod := mul_nonneg (sq_nonneg u)
      (show 0 ≤ 1 - 9 * u ^ 2 by nlinarith)
    nlinarith
  calc
    taoGeom2CenteredExpMoment t = (1 - u ^ 2)⁻¹ :=
      taoGeom2CenteredExpMoment_eq_one_sub_sq_inv hadm
    _ ≤ 1 + (9 / 8 : ℝ) * u ^ 2 := hinv
    _ ≤ Real.exp ((9 / 8 : ℝ) * u ^ 2) := by
      simpa only [add_comm] using Real.add_one_le_exp ((9 / 8 : ℝ) * u ^ 2)
    _ ≤ Real.exp (3 * t ^ 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])

theorem centeredListMoment_le_exp_three_sq (N : ℕ) {t : ℝ}
    (ht : |t| ≤ 1 / 4) :
    (∑' as : List ℕ+, (geom2PNatListPMF N as).toReal *
      Real.exp (t * taoGeom2CenteredListWeight as)) ≤
      Real.exp (3 * t ^ 2 * N) := by
  have hadm : Real.exp t < 2 := by
    have hh := exp_sub_one_abs_le_four_thirds ht
    have ha := le_abs_self (Real.exp t - 1)
    linarith
  rw [(geom2PNatListPMF_centeredExpMoment N hadm).2]
  calc
    taoGeom2CenteredExpMoment t ^ N ≤ Real.exp (3 * t ^ 2) ^ N :=
      pow_le_pow_left₀ (taoGeom2CenteredExpMoment_nonneg t)
        (centeredMoment_le_exp_three_sq ht) N
    _ = Real.exp (3 * t ^ 2 * N) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end SyracuseReport
