import SelectedKernel
import SelectedIncrementSummability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-! Quantitative length comparisons and vanishing valuation windows for the
actual fixed-block schedule. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem prefixDepth_real_upper (N : ℕ) :
    (prefixDepth N : ℝ) ≤ 200 * (blockLength N : ℝ) := by
  induction N with
  | zero => norm_num [prefixDepth, blockLength, baseBlockLength]
  | succ N ih =>
      have hb := (blockLength_real_step_bounds N).1
      rw [prefixDepth, Nat.cast_add]
      linarith

theorem prefixDepth_upper (N : ℕ) : prefixDepth N ≤ 200 * blockLength N := by
  exact_mod_cast prefixDepth_real_upper N

theorem index_le_prefixDepth (N : ℕ) : N ≤ prefixDepth N := by
  have hb : 1 ≤ baseBlockLength := by norm_num [baseBlockLength]
  exact (Nat.le_mul_of_pos_right N hb).trans (prefixDepth_lower N)

theorem flexible_length_le_block (N t : ℕ) (ht : t ≤ 2 * blockLength N) :
    prefixDepth N + t ≤ 202 * blockLength N := by
  have h := prefixDepth_upper N
  omega

theorem flexible_length_le_terminal (N t : ℕ) (hkt : terminalDepth N ≤ t)
    (ht : t ≤ 2 * blockLength N) : prefixDepth N + t ≤ 1616 * t := by
  have hb := (terminalDepth_real_bounds N).1
  have htr : (terminalDepth N : ℝ) ≤ t := by exact_mod_cast hkt
  have hlen : ((prefixDepth N + t : ℕ) : ℝ) ≤ 202 * blockLength N := by
    exact_mod_cast flexible_length_le_block N t ht
  have h : ((prefixDepth N + t : ℕ) : ℝ) ≤ 1616 * t := by linarith
  exact_mod_cast h

theorem terminalDepth_ge_250000 (N : ℕ) : 250000 ≤ terminalDepth N := by
  have hb := baseBlockLength_le N
  norm_num [baseBlockLength] at hb
  unfold terminalDepth
  omega

theorem terminal_pruning_window_bounds {δ : ℝ} (hδ : 0 < δ)
    (hδsmall : δ ≤ 1 / 10000) (N t : ℕ) (hkt : terminalDepth N ≤ t)
    (htN : t ≤ 2 * blockLength N) :
    0 < Nat.ceil (δ * ((prefixDepth N + t : ℕ) : ℝ)) ∧
      δ * ((prefixDepth N + t : ℕ) : ℝ) ≤ Nat.ceil (δ * ((prefixDepth N + t : ℕ) : ℝ)) ∧
      (Nat.ceil (δ * ((prefixDepth N + t : ℕ) : ℝ)) : ℝ) ≤ (3 / 2 : ℝ) * t := by
  have htlarge : 250000 ≤ t := (terminalDepth_ge_250000 N).trans hkt
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlen : ((prefixDepth N + t : ℕ) : ℝ) ≤ 1616 * t := by
    exact_mod_cast flexible_length_le_terminal N t hkt htN
  have hhpos : (0 : ℝ) < ((prefixDepth N + t : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < prefixDepth N + t by omega)
  have hx : 0 < δ * ((prefixDepth N + t : ℕ) : ℝ) := mul_pos hδ hhpos
  have hlo := Nat.le_ceil (δ * ((prefixDepth N + t : ℕ) : ℝ))
  have hm0 : (0 : ℝ) < Nat.ceil (δ * ((prefixDepth N + t : ℕ) : ℝ)) := hx.trans_le hlo
  refine ⟨by exact_mod_cast hm0, hlo, ?_⟩
  have hhalf : δ * 1616 ≤ (1 / 2 : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hlen hδ.le
  have hhalfprod := mul_le_mul_of_nonneg_right hhalf ht0.le
  have hceil := (Nat.ceil_lt_add_one hx.le).le
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  nlinarith

theorem terminal_rejection_exponent_le_linear {h t m δ : ℝ}
    (ht : 0 < t) (hth : t ≤ h) (hδ : 0 ≤ δ) (hm : δ * h ≤ m) :
    -(m ^ 2) / (12 * t) ≤ -(δ ^ 2 * h) / 12 := by
  have hh : 0 < h := ht.trans_le hth
  have hx : 0 ≤ δ * h := mul_nonneg hδ hh.le
  have hsq := pow_le_pow_left₀ hx hm 2
  have hprod := mul_le_mul_of_nonneg_left hth (show 0 ≤ δ ^ 2 * h by positivity)
  apply (div_le_div_iff₀ (by positivity : 0 < 12 * t) (by norm_num : (0 : ℝ) < 12)).mpr
  nlinarith

theorem blockLength_two_fifths_geometric_lower (N : ℕ) :
    ((201 / 200 : ℝ) ^ (2 / 5 : ℝ)) ^ N ≤ (blockLength N : ℝ) ^ (2 / 5 : ℝ) := by
  have hg := (blockLength_geometric_bounds N).1
  have hb : (1 : ℝ) ≤ baseBlockLength := by norm_num [baseBlockLength]
  have hlo : (201 / 200 : ℝ) ^ N ≤ (blockLength N : ℝ) := by
    nlinarith [show 0 ≤ (201 / 200 : ℝ) ^ N by positivity]
  rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 201 / 200)]
  exact Real.rpow_le_rpow (by positivity) hlo (by norm_num)

theorem prefixWindow_selectedDepth_ratio_bound (N : ℕ) :
    (prefixWindow N : ℝ) / (selectedDepth N : ℝ) ≤
      16 * N / (blockLength N : ℝ) ^ (2 / 5 : ℝ) := by
  let b : ℝ := blockLength N
  let d : ℝ := selectedDepth N
  have hb : 0 < b := lt_of_lt_of_le (by norm_num) (blockLength_real_ge_one N)
  have hd : b / 8 ≤ d := by
    have ht := (terminalDepth_real_bounds N).1
    have hp : (0 : ℝ) ≤ prefixDepth N := by positivity
    dsimp [d, selectedDepth]
    rw [Nat.cast_add]
    linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hpow : 0 < b ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hb _
  have hmul : b ^ (3 / 5 : ℝ) * b ^ (2 / 5 : ℝ) = b := by
    rw [← Real.rpow_add hb]
    norm_num
  have hw := mul_le_mul_of_nonneg_right (prefixWindow_real_bound N) hpow.le
  change (prefixWindow N : ℝ) * b ^ (2 / 5 : ℝ) ≤
    2 * (N : ℝ) * b ^ (3 / 5 : ℝ) * b ^ (2 / 5 : ℝ) at hw
  rw [mul_assoc, hmul] at hw
  have hnd := mul_le_mul_of_nonneg_left hd (show 0 ≤ 16 * (N : ℝ) by positivity)
  change (prefixWindow N : ℝ) / d ≤ 16 * (N : ℝ) / b ^ (2 / 5 : ℝ)
  apply (div_le_div_iff₀ hdpos hpow).mpr
  nlinarith

theorem prefixWindow_selectedDepth_ratio_tendsto :
    Tendsto (fun N => (prefixWindow N : ℝ) / (selectedDepth N : ℝ)) atTop (𝓝 0) := by
  have hR : (1 : ℝ) < (201 / 200 : ℝ) ^ (2 / 5 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hlim : Tendsto
      (fun N : ℕ => 16 * (N : ℝ) / ((201 / 200 : ℝ) ^ (2 / 5 : ℝ)) ^ N)
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 hR).const_mul 16
  apply squeeze_zero (fun N => by positivity) _ hlim
  intro N
  apply (prefixWindow_selectedDepth_ratio_bound N).trans
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (blockLength_two_fifths_geometric_lower N)

theorem selectedKernelConstant_quadratic_length_bound (N t : ℕ)
    (hkt : terminalDepth N ≤ t) :
    selectedKernelConstant N ≤
      (32 * ((prefixDepth N + t : ℕ) : ℝ) ^ 2 + 1) *
        ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) := by
  let h : ℝ := prefixDepth N + t
  have hN : (N : ℝ) ≤ h := by
    have hi : (N : ℝ) ≤ prefixDepth N := by exact_mod_cast index_le_prefixDepth N
    have ht0 : (0 : ℝ) ≤ t := by positivity
    dsimp [h]
    linarith
  have hb : (blockLength N : ℝ) ≤ 8 * h := by
    have ht := (terminalDepth_real_bounds N).1
    have htr : (terminalDepth N : ℝ) ≤ t := by exact_mod_cast hkt
    have hp : (0 : ℝ) ≤ prefixDepth N := by positivity
    dsimp [h]
    linarith
  have hpow : (blockLength N : ℝ) ^ (3 / 5 : ℝ) ≤ (blockLength N : ℝ) :=
    Real.rpow_le_self_of_one_le (blockLength_real_ge_one N) (by norm_num)
  have hprod := mul_le_mul hN (hpow.trans hb) (by positivity :
    0 ≤ (blockLength N : ℝ) ^ (3 / 5 : ℝ)) (by dsimp [h]; positivity)
  have hfactor : 4 * (N : ℝ) * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1 ≤
      32 * h ^ 2 + 1 := by nlinarith
  unfold selectedKernelConstant
  have hcast : ((prefixDepth N + t : ℕ) : ℝ) = h := by simp only [h, Nat.cast_add]
  rw [hcast]
  exact mul_le_mul_of_nonneg_right hfactor (by positivity)

theorem quadratic_pruning_envelope_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun h : ℝ => (32 * h ^ 2 + 1) * Real.exp (-a * h)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun h : ℝ => h ^ 2 * Real.exp (-a * h)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) a ha
  have h0 : Tendsto (fun h : ℝ => Real.exp (-a * h)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) a ha
  have hl : Tendsto (fun h : ℝ =>
      32 * (h ^ 2 * Real.exp (-a * h)) + Real.exp (-a * h)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h2.const_mul 32).add h0
  convert hl using 1
  funext h
  ring

theorem selected_mixing_bound_le_increment (C6 : ℝ)
    (hp : ∀ N, blockProbability N ≤ 1) (N : ℕ) :
    selectedKernelConstant N * ((2 / 3 : ℝ) * C6 / (terminalDepth N : ℝ) ^ 6) ≤
      selectedIncrementBound C6 N := by
  have hK : 0 ≤ (2 / 3 : ℝ) * selectedKernelConstant N := by
    unfold selectedKernelConstant
    positivity
  have hnonneg : 0 ≤ 1 - blockProbability N := sub_nonneg.mpr (hp N)
  unfold selectedIncrementBound
  calc
    selectedKernelConstant N * ((2 / 3 : ℝ) * C6 / (terminalDepth N : ℝ) ^ 6) =
        (2 / 3 : ℝ) * selectedKernelConstant N * (C6 / (terminalDepth N : ℝ) ^ 6) := by ring
    _ ≤ (2 / 3 : ℝ) * selectedKernelConstant N *
        (C6 / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnonneg) hK

theorem selected_mixing_bound_tendsto {C6 : ℝ} (hC : 0 ≤ C6)
    (hp : ∀ N, blockProbability N ≤ 1)
    (hreject : ∀ N, 1 - blockProbability N ≤
      2 * Real.exp (-((blockLength N : ℝ) ^ (1 / 5 : ℝ)) / 12)) :
    Tendsto (fun N => selectedKernelConstant N *
      ((2 / 3 : ℝ) * C6 / (terminalDepth N : ℝ) ^ 6)) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => by unfold selectedKernelConstant; positivity)
    (selected_mixing_bound_le_increment C6 hp)
  exact (summable_selectedIncrementBound hC hp hreject).tendsto_atTop_zero

end SyracuseReport
