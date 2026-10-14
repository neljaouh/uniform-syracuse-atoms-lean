import ResearchIncrementMoments
import Mathlib.Analysis.PSeries

/-! Summable Lq norm bounds for the actual Syracuse density increments. -/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

/-- Algebraic interpolation of a sufficiently fast L1 rate with quadratic
L2 energy produces an inverse-square norm bound. -/
theorem interpolated_power_bound (q C t : ℝ) (A : ℕ)
    (hq : 0 < q) (hq2 : q < 2) (hq1 : 1 ≤ q) (hC : 0 ≤ C) (ht : 1 ≤ t)
    (hA : 2 * q + 2 * (q - 1) ≤ (A : ℝ) * (2 - q)) :
    ((C / t ^ A) ^ (2 - q) * (80 * t ^ 2) ^ (q - 1)) ^ (1 / q) ≤
      (C ^ (2 - q) * (80 : ℝ) ^ (q - 1)) ^ (1 / q) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hexp : (-(A : ℝ) * (2 - q) + 2 * (q - 1)) * (1 / q) ≤ -2 := by
    rw [mul_one_div, div_le_iff₀ hq]
    linarith
  have hprod : (C / t ^ A) ^ (2 - q) * (80 * t ^ 2) ^ (q - 1) =
      (C ^ (2 - q) * (80 : ℝ) ^ (q - 1)) *
        t ^ (-(A : ℝ) * (2 - q) + 2 * (q - 1)) := by
    rw [Real.div_rpow hC (pow_nonneg ht0.le _) (2 - q),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 80) (sq_nonneg t),
      ← Real.rpow_natCast t A, ← Real.rpow_natCast t 2,
      ← Real.rpow_mul ht0.le, ← Real.rpow_mul ht0.le]
    rw [Real.rpow_add ht0, neg_mul, Real.rpow_neg ht0.le]
    ring
  rw [hprod, Real.mul_rpow (by positivity) (Real.rpow_nonneg ht0.le _),
    ← Real.rpow_mul ht0.le]
  have hpow := Real.rpow_le_rpow_of_exponent_le ht hexp
  have hmul := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (by positivity : 0 ≤ C ^ (2 - q) * (80 : ℝ) ^ (q - 1)) (1 / q))
  convert hmul using 1
  rw [show (-2 : ℝ) = -(2 : ℝ) from rfl, Real.rpow_neg ht0.le, Real.rpow_two]
  rfl

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

/-- An inverse-square majorant, with a finite constant for each q<2. -/
theorem densityIncrement_eLpNorm_bound (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      eLpNorm (densityIncrement n) (ENNReal.ofReal q) unitHaar ≤
        ENNReal.ofReal (K / (n : ℝ) ^ 2) := by
  have hq : 0 < q := by linarith
  have ha : 0 < 2 - q := by linarith
  obtain ⟨A, hA⟩ := exists_nat_gt (max 0 ((2 * q + 2 * (q - 1)) / (2 - q)))
  have hApos : 0 < A := by
    have : (0 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
    exact_mod_cast this
  have hAneed : 2 * q + 2 * (q - 1) ≤ (A : ℝ) * (2 - q) := by
    have h := (div_lt_iff₀ ha).mp (lt_of_le_of_lt (le_max_right _ _) hA)
    exact h.le
  obtain ⟨C, hC, hbound⟩ := densityIncrement_subcritical_moment_bound q hq1 hq2 A hApos
  let K := (C ^ (2 - q) * (80 : ℝ) ^ (q - 1)) ^ (1 / q)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := ENNReal.rpow_le_rpow (hbound n hn) (by positivity : 0 ≤ 1 / q)
  have hnorm : eLpNorm (densityIncrement n) (ENNReal.ofReal q) unitHaar =
      (∫⁻ x, ENNReal.ofReal |densityIncrement n x| ^ q ∂unitHaar) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) (by simp),
      ENNReal.toReal_ofReal hq.le]
    simp only [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  rw [hnorm]
  have hreal :
      (ENNReal.ofReal (C / (n : ℝ) ^ A) ^ (2 - q) *
        ENNReal.ofReal (80 * (n : ℝ) ^ 2) ^ (q - 1)) ^ (1 / q) =
      ENNReal.ofReal (((C / (n : ℝ) ^ A) ^ (2 - q) *
        (80 * (n : ℝ) ^ 2) ^ (q - 1)) ^ (1 / q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ha.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith : 0 ≤ q - 1),
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  rw [hreal] at h
  exact h.trans (ENNReal.ofReal_le_ofReal
    (interpolated_power_bound q C n A hq hq2 hq1.le hC hn1 hAneed))

/-- This is summability of the norms themselves, not just the q-th moments. -/
theorem densityIncrement_eLpNorm_tsum_ne_top (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    (∑' n : ℕ, eLpNorm (densityIncrement (n + 1)) (ENNReal.ofReal q) unitHaar) ≠ ∞ := by
  obtain ⟨K, hK, hb⟩ := densityIncrement_eLpNorm_bound q hq1 hq2
  have hs0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hs0
  have hs : Summable (fun n : ℕ => K / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    convert hs1.mul_left K using 1
    funext n
    ring
  exact ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun n => hb (n + 1) (by omega)))
    hs.tsum_ofReal_ne_top.lt_top)

end SyracuseReport
