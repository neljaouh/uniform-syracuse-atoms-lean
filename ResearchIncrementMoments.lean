import ResearchInterpolation

/-! Subcritical moment estimates for the actual density increments. -/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem integrable_densityIncrement (n : ℕ) :
    Integrable (densityIncrement n) unitHaar :=
  (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).sub
    (integrable_cylinderFunction unitHaar n (density n))

/-- Both inputs are instantiated at the actual Syracuse densities. The
remaining limit argument must still sum the resulting Lq norms. -/
theorem densityIncrement_subcritical_moment_bound
    (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫⁻ x, ENNReal.ofReal |densityIncrement n x| ^ q ∂unitHaar) ≤
        ENNReal.ofReal (C / (n : ℝ) ^ A) ^ (2 - q) *
          ENNReal.ofReal (80 * (n : ℝ) ^ 2) ^ (q - 1) := by
  obtain ⟨C, hC, hL1⟩ := densityIncrement_L1_all_orders A hA
  refine ⟨C, hC, ?_⟩
  intro n hn
  have habs := (integrable_densityIncrement n).abs
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal |densityIncrement n x|) unitHaar :=
    habs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfirst : (∫⁻ x, ENNReal.ofReal |densityIncrement n x| ∂unitHaar) =
      ENNReal.ofReal (∫ x, |densityIncrement n x| ∂unitHaar) :=
    (ofReal_integral_eq_lintegral_ofReal habs
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))).symm
  have hsecond : (∫⁻ x, ENNReal.ofReal |densityIncrement n x| ^ (2 : ℝ) ∂unitHaar) =
      ENNReal.ofReal (∫ x, densityIncrement n x ^ 2 ∂unitHaar) := by
    have heq : (fun x => ENNReal.ofReal |densityIncrement n x| ^ (2 : ℝ)) =
        (fun x => ENNReal.ofReal (densityIncrement n x ^ 2)) := by
      funext x
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
    rw [heq]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_densityIncrement_sq n)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))).symm
  have h := lintegral_subcritical_interpolation unitHaar
    (fun x => ENNReal.ofReal |densityIncrement n x|) hmeas q hq1 hq2
  rw [hfirst, hsecond] at h
  refine h.trans (mul_le_mul' ?_ ?_)
  · exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hL1 n hn)) (by linarith)
  · exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (densityIncrement_L2_sq_le n hn)) (by linarith)

end SyracuseReport
