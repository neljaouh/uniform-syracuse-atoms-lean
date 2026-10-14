import ResearchDensitySpectrum
import OffsetLaws

/-! Exact manuscript contracts for sharp density integrability and its
energy and unit-offset consequences. Paper labels, rather than historical
Lean theorem letters, identify the corresponding manuscript results. -/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

def ExactIntegrabilityStatement : Prop :=
  ∀ f : PadicInt 3 → ℝ, Integrable f unitHaar →
    (∀ᵐ x ∂unitHaar, 0 ≤ f x) →
    unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) = unitDensityMeasure →
    (∀ q : ℝ, 1 ≤ q → (MemLp f (ENNReal.ofReal q) unitHaar ↔ q < 2)) ∧
    IsLUB {q : ℝ | 1 ≤ q ∧ MemLp f (ENNReal.ofReal q) unitHaar} 2

theorem paper_exact_integrability : ExactIntegrabilityStatement := by
  intro f hfi hpos hmodel
  exact ⟨actual_density_memLp_iff f hfi hpos hmodel,
    actual_density_critical_exponent_two f hfi hpos hmodel⟩

def CollisionUpperStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    collisionEnergy n ≤ (608 / 243 : ℝ) * (n : ℝ) ^ 2 +
      (392 / 81 : ℝ) * n + 136 / 243 ∧
    (608 / 243 : ℝ) * (n : ℝ) ^ 2 + (392 / 81 : ℝ) * n + 136 / 243 ≤
      8 * (n : ℝ) ^ 2

theorem paper_collision_upper : CollisionUpperStatement := by
  intro n hn
  refine ⟨collisionEnergy_explicit_upper n hn, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  nlinarith

def OffsetIntegrabilityStatement : Prop :=
  ∀ u : (PadicInt 3)ˣ,
    (∀ q : ℝ, 1 ≤ q → (MemLp (offsetDensity u) (ENNReal.ofReal q) unitHaar ↔ q < 2)) ∧
    IsLUB {q : ℝ | 1 ≤ q ∧ MemLp (offsetDensity u) (ENNReal.ofReal q) unitHaar} 2

theorem paper_offset_integrability : OffsetIntegrabilityStatement := by
  intro u
  have hiff (q : ℝ) (hq : 1 ≤ q) :
      MemLp (offsetDensity u) (ENNReal.ofReal q) unitHaar ↔ q < 2 :=
    (offset_memLp_iff u unitDensityFunction (ENNReal.ofReal q)).trans
      (unitDensityFunction_memLp_iff q hq)
  refine ⟨hiff, ?_⟩
  apply lp_critical_exponent_is_two
  · intro q hq1 hq2
    exact (hiff q hq1).mpr hq2
  · exact offsetDensity_not_memLp_two u

end SyracuseReport
