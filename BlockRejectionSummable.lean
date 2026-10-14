import BlockGrowth
import BlockProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Summability of the stretched exponential error on the geometric block
schedule. The rejection estimate itself is proved in BlockAcceptance. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem summable_blockLength_inv :
    Summable (fun j => (blockLength j : ℝ)⁻¹) := by
  have hs : Summable (fun j : ℕ =>
      (baseBlockLength : ℝ)⁻¹ * (200 / 201 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(200 / 201 : ℝ)‖ < 1)).mul_left _
  apply hs.of_nonneg_of_le (fun j => by positivity)
  intro j
  have h := (blockLength_geometric_bounds j).1
  have hbase : (0 : ℝ) < baseBlockLength := by norm_num [baseBlockLength]
  have hprod : 0 < (baseBlockLength : ℝ) * (201 / 200 : ℝ) ^ j := by positivity
  calc
    (blockLength j : ℝ)⁻¹ ≤
        ((baseBlockLength : ℝ) * (201 / 200 : ℝ) ^ j)⁻¹ :=
      inv_le_inv₀ (hprod.trans_le h) hprod |>.2 h
    _ = (baseBlockLength : ℝ)⁻¹ * (200 / 201 : ℝ) ^ j := by
      rw [mul_inv, ← inv_pow]
      norm_num

theorem summable_block_rejection_bound :
    Summable (fun j => 2 * Real.exp (-((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12)) := by
  have hbtop : Tendsto (fun j => (blockLength j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp blockLength_strictMono.tendsto_atTop
  have hxtop : Tendsto (fun j => (blockLength j : ℝ) ^ (1 / 5 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hbtop
  have hsmall := (isLittleO_exp_neg_mul_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 12) (-5)).eventuallyLE
  have hev := hxtop.eventually hsmall
  have hs := summable_blockLength_inv.mul_left 2
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hev] with j hj
  have hb : (0 : ℝ) < blockLength j := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 200) (blockLength_ge_200 j))
  have heq : ((blockLength j : ℝ) ^ (1 / 5 : ℝ)) ^ (-5 : ℝ) =
      (blockLength j : ℝ)⁻¹ := by
    rw [← Real.rpow_mul hb.le,
      show (1 / 5 : ℝ) * (-5 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, heq,
    abs_of_nonneg (show 0 ≤ (blockLength j : ℝ)⁻¹ by positivity)] at hj
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤
    2 * Real.exp (-((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12) by positivity)]
  have he : -(1 / 12 : ℝ) * (blockLength j : ℝ) ^ (1 / 5 : ℝ) =
      -((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12 := by ring
  rw [he] at hj
  exact mul_le_mul_of_nonneg_left hj (by norm_num)

theorem prefixProbability_inf_pos_of_rejection_bound
    (hbound : ∀ j, 1 - blockProbability j ≤
      2 * Real.exp (-((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12)) :
    0 < sInf (Set.range prefixProbability) := by
  apply prefixProbability_inf_pos_of_summable
  apply summable_block_rejection_bound.of_nonneg_of_le
  · intro j
    exact sub_nonneg.mpr (blockProbability_le_one j)
  · exact hbound

end SyracuseReport
