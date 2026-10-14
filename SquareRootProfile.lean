import BlockGrowth
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The square-root logarithmic valuation profile, including the rounding,
Chernoff exponent and geometric summability estimates used below. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators

noncomputable def sqrtLogProfile (x : ℝ) : ℝ := Real.sqrt (x * Real.log x)
noncomputable def sqrtLogWindow (n : ℕ) : ℕ := Nat.ceil (12 * sqrtLogProfile n)

theorem sqrtLogProfile_nonneg (x : ℝ) : 0 ≤ sqrtLogProfile x := Real.sqrt_nonneg _

theorem sqrtLogProfile_sq {x : ℝ} (hx : 1 ≤ x) :
    sqrtLogProfile x ^ 2 = x * Real.log x :=
  Real.sq_sqrt (mul_nonneg (by linarith) (Real.log_nonneg hx))

theorem sqrtLogProfile_pos {x : ℝ} (hx : 1 < x) : 0 < sqrtLogProfile x :=
  Real.sqrt_pos.2 (mul_pos (by linarith) (Real.log_pos hx))

theorem sqrtLogProfile_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    sqrtLogProfile x ≤ sqrtLogProfile y := by
  apply Real.sqrt_le_sqrt
  exact mul_le_mul hxy (Real.log_le_log (by linarith) hxy)
    (Real.log_nonneg hx) (by linarith)

theorem sqrtLogProfile_ge_one {x : ℝ} (hx : 2 ≤ x) : 1 ≤ sqrtLogProfile x := by
  have hpos : 0 < x := by linarith
  have hlog := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hpos.le
  have heq : x * (1 - x⁻¹) = x - 1 := by field_simp <;> ring
  rw [heq] at hlog
  have hsq := sqrtLogProfile_sq (by linarith : 1 ≤ x)
  have hn := sqrtLogProfile_nonneg x
  nlinarith

theorem sqrtLogProfile_ge_sqrt {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.sqrt x ≤ sqrtLogProfile x := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
  apply Real.sqrt_le_sqrt
  nlinarith

theorem sqrtLogProfile_div_rpow_tendsto {r : ℝ} (hr : 1 / 2 < r) :
    Tendsto (fun x : ℝ => sqrtLogProfile x / x ^ r) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
    (show 0 < r - 1 / 2 by linarith)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold sqrtLogProfile
  rw [Real.sqrt_mul hx.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have heq : x ^ r = x ^ (1 / 2 : ℝ) * x ^ (r - 1 / 2) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [heq]
  field_simp

theorem sqrtLogProfile_tendsto : Tendsto sqrtLogProfile atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ Real.tendsto_sqrt_atTop
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  exact sqrtLogProfile_ge_sqrt hx

theorem sqrtLogProfile_scale_eight {x : ℝ} (hx : 2 ≤ x) :
    sqrtLogProfile (8 * x) ≤ 8 * sqrtLogProfile x := by
  have hxpos : 0 < x := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  have hl : Real.log (8 * x) ≤ 4 * Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne', show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]
    norm_num at *
    linarith
  have hsq := sqrtLogProfile_sq (by linarith : 1 ≤ x)
  have hsq8 := sqrtLogProfile_sq (by linarith : 1 ≤ 8 * x)
  have hp := mul_le_mul_of_nonneg_left hl (show 0 ≤ 8 * x by positivity)
  have hn := sqrtLogProfile_nonneg x
  have hn8 := sqrtLogProfile_nonneg (8 * x)
  nlinarith [sq_nonneg (sqrtLogProfile x)]

theorem sqrtLogWindow_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < sqrtLogWindow n ∧ 12 * sqrtLogProfile n ≤ sqrtLogWindow n ∧
      (sqrtLogWindow n : ℝ) ≤ 24 * sqrtLogProfile n := by
  have hge := sqrtLogProfile_ge_one (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  have hlo : 12 * sqrtLogProfile n ≤ (sqrtLogWindow n : ℝ) := Nat.le_ceil _
  have hhi : (sqrtLogWindow n : ℝ) ≤ 2 * (12 * sqrtLogProfile n) :=
    Nat.ceil_le_two_mul (by linarith)
  refine ⟨?_, hlo, by linarith⟩
  have hpos : (0 : ℝ) < sqrtLogWindow n := by linarith
  exact_mod_cast hpos

theorem sqrtLogWindow_small_eventually :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, h ≤ 1616 * t →
      (sqrtLogWindow h : ℝ) ≤ (3 / 2 : ℝ) * t := by
  have hlim := (sqrtLogProfile_div_rpow_tendsto (r := 1) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  simp only [Real.rpow_one, Function.comp_apply] at hlim
  have hev := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / (24 * 1616)))
  filter_upwards [hev, eventually_ge_atTop 2] with h hh hh2
  intro t hht
  have hp : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hr := (div_le_iff₀ hp).1 hh.le
  have htR : (h : ℝ) ≤ 1616 * t := by exact_mod_cast hht
  have hw := (sqrtLogWindow_bounds hh2).2.2
  linarith

theorem sqrtLogWindow_le_subpower_eventually :
    ∀ᶠ h : ℕ in atTop, sqrtLogWindow h ≤ Nat.ceil ((h : ℝ) ^ (3 / 5 : ℝ)) := by
  have hlim := (sqrtLogProfile_div_rpow_tendsto (r := 3 / 5) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hev := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 24))
  filter_upwards [hev, eventually_ge_atTop 2] with h hh hh2
  have hp : (0 : ℝ) < (h : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < h by omega)) _
  have hr := (div_le_iff₀ hp).1 hh.le
  have hw := (sqrtLogWindow_bounds hh2).2.2
  apply Nat.ceil_le.mpr
  exact (show 12 * sqrtLogProfile h ≤ (h : ℝ) ^ (3 / 5 : ℝ) by
    nlinarith [sqrtLogProfile_nonneg h]).trans (Nat.le_ceil _)

theorem sqrtLog_rejection_bound {h t : ℕ} (hh : 2 ≤ h) (ht : 0 < t) (hth : t ≤ h) :
    Real.exp (-((sqrtLogWindow h : ℝ) ^ 2) / (12 * (t : ℝ))) ≤
      1 / (h : ℝ) ^ 12 := by
  have hp : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hs := sqrtLogProfile_sq (by exact_mod_cast (show 1 ≤ h by omega) : (1 : ℝ) ≤ h)
  have hm := (sqrtLogWindow_bounds hh).2.1
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) (sqrtLogProfile_nonneg h)) hm 2
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ h by exact_mod_cast (show 1 ≤ h by omega))
  have hmul := mul_le_mul_of_nonneg_right (show (t : ℝ) ≤ h by exact_mod_cast hth) hlog
  have he : -((sqrtLogWindow h : ℝ) ^ 2) / (12 * (t : ℝ)) ≤ -12 * Real.log h := by
    apply (div_le_iff₀ (show 0 < 12 * (t : ℝ) by positivity)).2
    nlinarith [hs]
  apply (Real.exp_le_exp.mpr he).trans_eq
  rw [show -12 * Real.log (h : ℝ) = -(Real.log ((h : ℝ) ^ 12)) by rw [Real.log_pow]; ring,
    Real.exp_neg, Real.exp_log (by positivity), one_div]

theorem blockLength_tendsto_atTop : Tendsto blockLength atTop atTop :=
  blockLength_strictMono.tendsto_atTop

theorem sqrtLogProfile_block_step (N : ℕ) :
    Real.sqrt (201 / 200 : ℝ) * sqrtLogProfile (blockLength N) ≤
      sqrtLogProfile (blockLength (N + 1)) := by
  let x : ℝ := blockLength N
  let y : ℝ := blockLength (N + 1)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (blockLength_ge_200 N).trans' (by norm_num : 1 ≤ 200)
  have hy : 1 ≤ y := by dsimp [y]; exact_mod_cast (blockLength_ge_200 (N+1)).trans' (by norm_num : 1 ≤ 200)
  have hscale : (201 / 200 : ℝ) * x ≤ y := (blockLength_real_step_bounds N).1
  have hxy : x ≤ y := by nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < x) hxy
  have hp : (201 / 200 : ℝ) * (x * Real.log x) ≤ y * Real.log y := by
    have h1 := mul_le_mul_of_nonneg_right hscale (Real.log_nonneg hx)
    have h2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ y by linarith)
    nlinarith
  have hsqx := sqrtLogProfile_sq hx
  have hsqy := sqrtLogProfile_sq hy
  have heq : (Real.sqrt (201 / 200 : ℝ) * sqrtLogProfile x) ^ 2 =
      (201 / 200 : ℝ) * (x * Real.log x) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num),hsqx]
  have hn := sqrtLogProfile_nonneg y
  have hn' : 0 ≤ Real.sqrt (201 / 200 : ℝ) * sqrtLogProfile x :=
    mul_nonneg (Real.sqrt_nonneg _) (sqrtLogProfile_nonneg _)
  change Real.sqrt (201 / 200 : ℝ) * sqrtLogProfile x ≤ sqrtLogProfile y
  nlinarith

end SyracuseReport
