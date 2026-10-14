import ResearchDensityIncrements
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! The Holder interpolation step used for the subcritical moments. -/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

theorem lintegral_subcritical_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h : α → ℝ≥0∞) (hh : AEMeasurable h μ)
    (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    (∫⁻ x, h x ^ q ∂μ) ≤
      (∫⁻ x, h x ∂μ) ^ (2 - q) * (∫⁻ x, h x ^ (2 : ℝ) ∂μ) ^ (q - 1) := by
  have ha : 0 < 2 - q := by linarith
  have hb : 0 < q - 1 := by linarith
  have hpq := Real.holderConjugate_one_div ha hb (by ring : (2 - q) + (q - 1) = 1)
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hh.pow_const (2 - q)) (hh.pow_const (2 * (q - 1)))
  have hpa : (2 - q) * (1 / (2 - q)) = 1 := by field_simp
  have hpb : (2 * (q - 1)) * (1 / (q - 1)) = 2 := by field_simp
  simp only [← ENNReal.rpow_mul, hpa, hpb, ENNReal.rpow_one, one_div_one_div] at H
  convert H using 1
  apply lintegral_congr
  intro x
  change h x ^ q = h x ^ (2 - q) * h x ^ (2 * (q - 1))
  rw [← ENNReal.rpow_add_of_nonneg (2 - q) (2 * (q - 1)) ha.le
    (by positivity : 0 ≤ 2 * (q - 1))]
  congr 1
  ring

end SyracuseReport
