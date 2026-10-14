import SmoothingPrinciple
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-! Sufficient polynomial mixing thresholds for the selected-word method.
The statements retain the geometric-scale and arithmetic-cost hypotheses. -/
namespace SyracuseReport
open Filter
open scoped Topology

theorem summable_negative_power_of_geometric_lower
    (b : ℕ → ℝ) (rho e : ℝ) (hrho : 1 < rho) (he : e < 0)
    (hb : ∀ n, rho ^ n ≤ b n) : Summable (fun n => (b n) ^ e) := by
  have hpos : 0 < rho := by linarith
  have hratio : ‖rho ^ e‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hrho he
  apply (summable_geometric_of_norm_lt_one hratio).of_nonneg_of_le
  · intro n
    exact (Real.rpow_pos_of_pos ((pow_pos hpos n).trans_le (hb n)) e).le
  · intro n
    have h := Real.rpow_le_rpow_of_nonpos (pow_pos hpos n) (hb n) he.le
    simpa only [Real.rpow_pow_comm hpos.le] using h

theorem summable_weighted_chernoff (b : ℕ → ℝ) (rho theta beta c : ℝ)
    (hrho : 1 < rho) (hbeta : 0 < beta) (hc : 0 < c)
    (hb : ∀ n, rho ^ n ≤ b n) :
    Summable (fun n => (b n) ^ theta * Real.exp (-c * (b n) ^ beta)) := by
  have hpos : 0 < rho := by linarith
  have hbpos : ∀ n, 0 < b n := fun n => (pow_pos hpos n).trans_le (hb n)
  have hbtop : Tendsto b atTop atTop :=
    tendsto_atTop_mono hb (tendsto_pow_atTop_atTop_of_one_lt hrho)
  have htop := (tendsto_rpow_atTop hbeta).comp hbtop
  let M : ℝ := (theta + 1) / beta
  have hbound := (isLittleO_exp_neg_mul_rpow_atTop hc (-M)).bound (by norm_num : (0 : ℝ) < 1)
  have hev := htop.eventually hbound
  refine (summable_negative_power_of_geometric_lower b rho (-1) hrho (by norm_num) hb).of_norm_bounded_eventually_nat ?_
  filter_upwards [hev] with n hn
  dsimp only [Function.comp_apply, Function.comp_def] at hn
  have hb0 : 0 ≤ b n := (hbpos n).le
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul,
    abs_of_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (hbpos n) beta) (-M))] at hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (b n) ^ theta * Real.exp (-c * (b n) ^ beta))]
  have hmul := mul_le_mul_of_nonneg_left hn
    (Real.rpow_nonneg (hbpos n).le theta)
  have heq : (b n) ^ theta * ((b n) ^ beta) ^ (-M) = (b n) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_mul (hbpos n).le, ← Real.rpow_add (hbpos n)]
    congr 1
    dsimp [M]
    field_simp [hbeta.ne']
    <;> ring
  exact hmul.trans_eq heq

theorem summable_mean_to_uniform_errors
    (b E : ℕ → ℝ) (rho theta alpha c C : ℝ)
    (hrho : 1 < rho) (htheta : 1 / 2 < theta) (hgap : theta < alpha)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ n, rho ^ n ≤ b n)
    (hEn : ∀ n, 0 ≤ E n)
    (herror : ∀ n, E n ≤ C * (b n) ^ theta *
      ((b n) ^ (-alpha) + Real.exp (-c * (b n) ^ (2 * theta - 1)))) :
    Summable E := by
  have hpos : ∀ n, 0 < b n := fun n => (pow_pos (by linarith : 0 < rho) n).trans_le (hb n)
  have hm := summable_negative_power_of_geometric_lower b rho (theta - alpha)
    hrho (by linarith) hb
  have hr := summable_weighted_chernoff b rho theta (2 * theta - 1) c
    hrho (by linarith) hc hb
  have hs := (hm.add hr).mul_left C
  apply hs.of_nonneg_of_le hEn
  intro n
  convert herror n using 1
  have hpower : (b n) ^ theta * (b n) ^ (-alpha) = (b n) ^ (theta - alpha) := by
    simpa only [sub_eq_add_neg] using (Real.rpow_add (hpos n) theta (-alpha)).symm
  rw [← hpower]
  ring

theorem exists_polynomial_smoothing_window (alpha : ℝ) (ha : 1 / 2 < alpha) :
    ∃ theta : ℝ, 1 / 2 < theta ∧ theta < 1 ∧ theta < alpha := by
  obtain ⟨theta, hlo, hhi⟩ := exists_between (lt_min ha (by norm_num : (1 / 2 : ℝ) < 1))
  exact ⟨theta, hlo, hhi.trans_le (min_le_right _ _), hhi.trans_le (min_le_left _ _)⟩

end SyracuseReport
