import BlockGrowth
import BlockWindowBounds
import PaperStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-! Summability of the actual selected-family increment majorant. -/

namespace SyracuseReport
open scoped Topology
open Filter

theorem blockLength_real_tendsto :
    Tendsto (fun N => (blockLength N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp blockLength_strictMono.tendsto_atTop

theorem block_rejection_envelope_eventually :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12) ≤
        1 / (blockLength N : ℝ) ^ 6 := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
    blockLength_real_tendsto
  have he := (isLittleO_exp_neg_mul_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 12) (-30)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ht.eventually he] with N hN
  have hb : (0 : ℝ) < blockLength N := lt_of_lt_of_le (by norm_num) (blockLength_real_ge_one N)
  have hr : ((blockLength N : ℝ) ^ (1 / 5 : ℝ)) ^ (-30 : ℝ) =
      1 / (blockLength N : ℝ) ^ 6 := by
    calc
      ((blockLength N : ℝ) ^ (1 / 5 : ℝ)) ^ (-30 : ℝ) =
          (blockLength N : ℝ) ^ (-(6 : ℝ)) := by
            rw [← Real.rpow_mul hb.le]
            congr 1
            norm_num
      _ = 1 / (blockLength N : ℝ) ^ 6 := by
            rw [Real.rpow_neg hb.le, Real.rpow_ofNat]
            simp only [one_div]
  have hexp : -(1 / 12 : ℝ) * (blockLength N : ℝ) ^ (1 / 5 : ℝ) =
      -((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12 := by ring
  dsimp only [Function.comp_def] at hN
  rw [hexp] at hN
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    one_mul, hr, abs_of_nonneg
      (show 0 ≤ 1 / (blockLength N : ℝ) ^ 6 by positivity)] using hN

theorem blockLength_inverse_fifth_geometric_bound (N : ℕ) :
    1 / (blockLength N : ℝ) ^ 5 ≤ ((200 / 201 : ℝ) ^ 5) ^ N := by
  have hg := (blockLength_geometric_bounds N).1
  have hb : (1 : ℝ) ≤ baseBlockLength := by norm_num [baseBlockLength]
  have hlow : (201 / 200 : ℝ) ^ N ≤ (blockLength N : ℝ) := by
    have hp : (0 : ℝ) ≤ (201 / 200 : ℝ) ^ N := by positivity
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity) hlow 5
  have hi := one_div_le_one_div_of_le (by positivity) hp
  convert hi using 1
  rw [← one_div_pow, ← one_div_pow]
  have hr : 1 / (201 / 200 : ℝ) = 200 / 201 := by norm_num
  rw [hr, ← pow_mul, ← pow_mul]
  congr 1
  omega

theorem summable_selected_geometric_majorant :
    Summable (fun N : ℕ => (4 * (N : ℝ) + 1) * ((200 / 201 : ℝ) ^ 5) ^ N) := by
  have hr : ‖(200 / 201 : ℝ) ^ 5‖ < 1 := by norm_num
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  convert (h1.mul_left 4).add h0 using 1
  funext N
  simp only [pow_one]
  ring

theorem selectedIncrementBound_nonneg {C6 : ℝ} (hC : 0 ≤ C6)
    (hp : ∀ N, blockProbability N ≤ 1) (N : ℕ) :
    0 ≤ selectedIncrementBound C6 N := by
  unfold selectedIncrementBound selectedKernelConstant
  have hreject : 0 ≤ 1 - blockProbability N := sub_nonneg.mpr (hp N)
  positivity

theorem selectedIncrementBound_le_inverse_fifth {C6 : ℝ} (hC : 0 ≤ C6)
    (hp : ∀ N, blockProbability N ≤ 1)
    (hreject : ∀ N, 1 - blockProbability N ≤
      2 * Real.exp (-((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12)) :
    ∀ᶠ N : ℕ in atTop,
      selectedIncrementBound C6 N ≤
        ((2 / 3 : ℝ) * ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) *
          (C6 * 8 ^ 6 + 2)) * (4 * (N : ℝ) + 1) /
            (blockLength N : ℝ) ^ 5 := by
  filter_upwards [block_rejection_envelope_eventually] with N he
  let b : ℝ := blockLength N
  let k : ℝ := terminalDepth N
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  have hb : 1 ≤ b := blockLength_real_ge_one N
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hkpos : 0 < k := by
    have hn : 0 < terminalDepth N := by have h := terminalDepth_pos N; omega
    dsimp [k]
    exact_mod_cast hn
  have hk : b / 8 ≤ k := (terminalDepth_real_bounds N).1
  have hm : (blockLength N : ℝ) ^ (3 / 5 : ℝ) ≤ b :=
    Real.rpow_le_self_of_one_le hb (by norm_num)
  have hkernel : selectedKernelConstant N ≤ (4 * (N : ℝ) + 1) * b * B := by
    unfold selectedKernelConstant
    dsimp [B]
    gcongr
    have hN : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have ht : C6 / k ^ 6 ≤ C6 * 8 ^ 6 / b ^ 6 := by
    calc
      C6 / k ^ 6 ≤ C6 / (b / 8) ^ 6 :=
        div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) hk 6)
      _ = C6 * 8 ^ 6 / b ^ 6 := by field_simp
  have hrej : 1 - blockProbability N ≤ 2 / b ^ 6 := by
    calc
      1 - blockProbability N ≤ 2 * Real.exp (-((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12) := hreject N
      _ ≤ 2 * (1 / b ^ 6) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 2 / b ^ 6 := by ring
  have hinside : C6 / k ^ 6 + (1 - blockProbability N) ≤ (C6 * 8 ^ 6 + 2) / b ^ 6 := by
    calc
      C6 / k ^ 6 + (1 - blockProbability N) ≤ C6 * 8 ^ 6 / b ^ 6 + 2 / b ^ 6 := add_le_add ht hrej
      _ = (C6 * 8 ^ 6 + 2) / b ^ 6 := by ring
  have hi0 : 0 ≤ C6 / k ^ 6 + (1 - blockProbability N) := by
    have h0 : 0 ≤ 1 - blockProbability N := sub_nonneg.mpr (hp N)
    positivity
  unfold selectedIncrementBound
  change (2 / 3 : ℝ) * selectedKernelConstant N *
    (C6 / k ^ 6 + (1 - blockProbability N)) ≤ _
  calc
    (2 / 3 : ℝ) * selectedKernelConstant N * (C6 / k ^ 6 + (1 - blockProbability N)) ≤
        (2 / 3 : ℝ) * ((4 * (N : ℝ) + 1) * b * B) * ((C6 * 8 ^ 6 + 2) / b ^ 6) := by
          gcongr
    _ = ((2 / 3 : ℝ) * B * (C6 * 8 ^ 6 + 2)) * (4 * (N : ℝ) + 1) / b ^ 5 := by
          field_simp

theorem summable_selectedIncrementBound {C6 : ℝ} (hC : 0 ≤ C6)
    (hp : ∀ N, blockProbability N ≤ 1)
    (hreject : ∀ N, 1 - blockProbability N ≤
      2 * Real.exp (-((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12)) :
    Summable (selectedIncrementBound C6) := by
  let K : ℝ := (2 / 3 : ℝ) *
    ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) * (C6 * 8 ^ 6 + 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine (summable_selected_geometric_majorant.mul_left K).of_norm_bounded_eventually_nat ?_
  filter_upwards [selectedIncrementBound_le_inverse_fifth hC hp hreject] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (selectedIncrementBound_nonneg hC hp N)]
  calc
    selectedIncrementBound C6 N ≤ K * (4 * (N : ℝ) + 1) / (blockLength N : ℝ) ^ 5 := hN
    _ ≤ K * ((4 * (N : ℝ) + 1) * ((200 / 201 : ℝ) ^ 5) ^ N) := by
      have h := blockLength_inverse_fifth_geometric_bound N
      have hcoeff : 0 ≤ K * (4 * (N : ℝ) + 1) := by positivity
      convert mul_le_mul_of_nonneg_left h hcoeff using 1 <;> ring

end SyracuseReport
