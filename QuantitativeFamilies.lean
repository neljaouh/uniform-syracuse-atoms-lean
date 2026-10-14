import CountingCompletion

/-! Subpower valuation windows at every sufficiently large word length.
All families are the concrete selected/pruned families of the paper. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def subpowerWindow (h : ℕ) : ℕ := Nat.ceil ((h : ℝ) ^ (3 / 5 : ℝ))

theorem prefixWindow_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N,
      (prefixWindow N : ℝ) ≤ K * (blockLength N : ℝ) ^ (3 / 5 : ℝ) := by
  let r : ℝ := (201 / 200 : ℝ) ^ (3 / 5 : ℝ)
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) (by norm_num)
  let K : ℝ := 2 / (r - 1)
  have hr0 : 0 < r - 1 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : K * r = K + 2 := by
    dsimp [K]
    field_simp [show r - 1 ≠ 0 by linarith]
    <;> ring
  refine ⟨K, hK, ?_⟩
  intro N
  induction N with
  | zero => simp [prefixWindow]; positivity
  | succ N ih =>
      have hg := (blockLength_real_step_bounds N).1
      have hp := Real.rpow_le_rpow (by positivity :
        (0 : ℝ) ≤ (201 / 200 : ℝ) * blockLength N) hg (by norm_num : (0 : ℝ) ≤ 3 / 5)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at hp
      have hmul := mul_le_mul_of_nonneg_left hp hK.le
      have hwin := blockWindow_real_le_two_rpow N
      rw [prefixWindow, Nat.cast_add]
      change (prefixWindow N : ℝ) + blockWindow N ≤ _
      change K * (r * (blockLength N : ℝ) ^ (3 / 5 : ℝ)) ≤ _ at hmul
      have heq : K * (r * (blockLength N : ℝ) ^ (3 / 5 : ℝ)) =
          (K + 2) * (blockLength N : ℝ) ^ (3 / 5 : ℝ) := by
        rw [← mul_assoc, hKr]
      rw [heq] at hmul
      linarith

theorem subpowerWindow_bounds (h : ℕ) (hh : 1 ≤ h) :
    0 < subpowerWindow h ∧ (h : ℝ) ^ (3 / 5 : ℝ) ≤ subpowerWindow h ∧
      (subpowerWindow h : ℝ) ≤ 2 * (h : ℝ) ^ (3 / 5 : ℝ) := by
  have hpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hlo := Nat.le_ceil ((h : ℝ) ^ (3 / 5 : ℝ))
  have hpow := Real.rpow_pos_of_pos hpos (3 / 5 : ℝ)
  have hceil : (0 : ℝ) < subpowerWindow h := hpow.trans_le hlo
  refine ⟨by exact_mod_cast hceil, hlo, ?_⟩
  exact Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans
    (Real.one_le_rpow (show (1 : ℝ) ≤ h by exact_mod_cast hh)
      (by norm_num : (0 : ℝ) ≤ 3 / 5)))

theorem subpowerWindow_small_eventually :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, h ≤ 1616 * t →
      (subpowerWindow h : ℝ) ≤ (3 / 2 : ℝ) * t := by
  have hlim : Tendsto (fun h : ℕ => (h : ℝ) ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hev := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3232))
  filter_upwards [hev, eventually_ge_atTop 1] with h hsmall hh
  intro t hht
  have hpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have heq : (h : ℝ) * (h : ℝ) ^ (-(2 / 5 : ℝ)) = (h : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      _ = (h : ℝ) ^ (1 : ℝ) * (h : ℝ) ^ (-(2 / 5 : ℝ)) := by rw [Real.rpow_one]
      _ = (h : ℝ) ^ ((1 : ℝ) + -(2 / 5 : ℝ)) := (Real.rpow_add hpos _ _).symm
      _ = _ := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hsmall.le hpos.le
  rw [heq] at hmul
  have hhtR : (h : ℝ) ≤ 1616 * t := by exact_mod_cast hht
  have hm := (subpowerWindow_bounds h hh).2.2
  have htR : (0 : ℝ) ≤ t := by positivity
  linarith

theorem subpower_rejection_exponent {h t : ℕ}
    (ht : 0 < t) (hth : t ≤ h) :
    -((subpowerWindow h : ℝ) ^ 2) / (12 * (t : ℝ)) ≤
      -((h : ℝ) ^ (1 / 5 : ℝ)) / 12 := by
  have hh : 1 ≤ h := by omega
  have hpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hm := (subpowerWindow_bounds h hh).2.1
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (h : ℝ) ^ (3 / 5 : ℝ)) hm 2
  have heq : ((h : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = h * (h : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    conv_rhs => lhs; rw [← Real.rpow_one (h : ℝ)]
    rw [← Real.rpow_add hpos]
    norm_num
  rw [heq] at hsq
  have hthR : (t : ℝ) ≤ h := by exact_mod_cast hth
  have hp := mul_le_mul_of_nonneg_left hthR
    (show (0 : ℝ) ≤ (h : ℝ) ^ (1 / 5 : ℝ) by positivity)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * t) (by norm_num : (0 : ℝ) < 12)).mpr
  nlinarith

theorem subpower_pruning_envelope_tendsto :
    Tendsto (fun h : ℕ => (32 * (h : ℝ) ^ 2 + 1) *
      Real.exp (-((h : ℝ) ^ (1 / 5 : ℝ)) / 12)) atTop (𝓝 0) := by
  have hx : Tendsto (fun h : ℕ => (h : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hpoly := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (10 : ℝ) (1 / 12 : ℝ) (by norm_num)).comp hx
  have hconst := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (hx.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 12)))
  have hsum := (hpoly.const_mul 32).add hconst
  convert hsum using 1
  · funext h
    simp only [Function.comp_apply]
    have heq : ((h : ℝ) ^ (1 / 5 : ℝ)) ^ (10 : ℝ) = (h : ℝ) ^ 2 := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ h)]
      norm_num
    rw [heq]
    have hexp1 : -(1 / 12 : ℝ) * (h : ℝ) ^ (1 / 5 : ℝ) =
        -((h : ℝ) ^ (1 / 5 : ℝ)) / 12 := by ring
    have hexp2 : -((1 / 12 : ℝ) * (h : ℝ) ^ (1 / 5 : ℝ)) =
        -((h : ℝ) ^ (1 / 5 : ℝ)) / 12 := by ring
    rw [hexp1, hexp2]
    ring
  · norm_num

end SyracuseReport
