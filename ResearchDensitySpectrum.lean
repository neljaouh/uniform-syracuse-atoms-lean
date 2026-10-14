import ResearchSubcriticalDensity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! The subcritical spectrum does not depend on the representative chosen
for the actual Syracuse density. -/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem actual_density_ae_eq (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) = unitDensityMeasure) :
    f =ᵐ[unitHaar] unitDensityFunction := by
  have h := (withDensity_eq_iff_of_sigmaFinite
    hfi.aemeasurable.ennreal_ofReal
    unitDensityFunction_integrable.aemeasurable.ennreal_ofReal).mp hmodel
  filter_upwards [h, hpos, unitDensityFunction_nonneg] with x hx hfx hgx
  have hreal := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal hfx, ENNReal.toReal_ofReal hgx] using hreal

/-- Complete strong-Lq spectrum for every nonnegative integrable density
representing the actual Syracuse probability with respect to unit Haar. -/
theorem actual_density_memLp_iff (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) = unitDensityMeasure)
    (q : ℝ) (hq : 1 ≤ q) : MemLp f (ENNReal.ofReal q) unitHaar ↔ q < 2 := by
  rw [memLp_congr_ae (actual_density_ae_eq f hfi hpos hmodel)]
  exact unitDensityFunction_memLp_iff q hq

theorem actual_density_critical_exponent_two (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) = unitDensityMeasure) :
    IsLUB {q : ℝ | 1 ≤ q ∧ MemLp f (ENNReal.ofReal q) unitHaar} 2 := by
  apply lp_critical_exponent_is_two
  · intro q hq1 hq2
    exact (actual_density_memLp_iff f hfi hpos hmodel q hq1).mpr hq2
  · exact model_not_memLp_two f hfi hpos hmodel

end SyracuseReport
