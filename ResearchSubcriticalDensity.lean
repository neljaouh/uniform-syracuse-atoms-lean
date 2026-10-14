import ResearchIncrementNorms
import ResearchLpConsequences
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The actual Syracuse density belongs to every Lq, 1 <= q < 2.
Summable increment norms give uniformly bounded finite-density norms;
convergence in measure to the already constructed L1 limit identifies
that limit without choosing a new density or assuming any Lq hypothesis. -/
namespace SyracuseReport
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem memLp_cylinderFunction (n : ℕ) (a : ZMod (3 ^ n) → ℝ) (p : ℝ≥0∞) :
    MemLp (cylinderFunction n a) p unitHaar := by
  classical
  apply MemLp.of_bound (integrable_cylinderFunction unitHaar n a).aestronglyMeasurable
    (∑ r : ZMod (3 ^ n), ‖a r‖)
  apply Eventually.of_forall
  intro x
  exact Finset.single_le_sum (fun r _ => norm_nonneg (a r))
    (Finset.mem_univ (PadicInt.toZModPow n x))

/-- Telescoping the actual successive densities in Lq. -/
theorem finite_density_eLpNorm_le (p : ℝ≥0∞) (hp : 1 ≤ p) (n : ℕ) :
    eLpNorm (cylinderFunction (n + 1) (density (n + 1))) p unitHaar ≤
      eLpNorm (cylinderFunction 1 (density 1)) p unitHaar +
        ∑ j ∈ Finset.range n, eLpNorm (densityIncrement (j + 1)) p unitHaar := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : cylinderFunction (n + 1 + 1) (density (n + 1 + 1)) =
          cylinderFunction (n + 1) (density (n + 1)) + densityIncrement (n + 1) := by
        funext x
        simp only [Pi.add_apply, densityIncrement]
        ring
      rw [heq, Finset.sum_range_succ]
      calc
        _ ≤ eLpNorm (cylinderFunction (n + 1) (density (n + 1))) p unitHaar +
              eLpNorm (densityIncrement (n + 1)) p unitHaar :=
          eLpNorm_add_le
            (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).aestronglyMeasurable
            (integrable_densityIncrement (n + 1)).aestronglyMeasurable hp
        _ ≤ _ := by
          have h := add_le_add ih (le_refl (eLpNorm (densityIncrement (n + 1)) p unitHaar))
          simpa only [add_assoc] using h

/-- Actual-law subcritical integrability; the density is exactly the one
used by Theorem B. -/
theorem unitDensityFunction_memLp_subcritical (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    MemLp unitDensityFunction (ENNReal.ofReal q) unitHaar := by
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using (ENNReal.ofReal_le_ofReal hq1.le)
  let B : ℝ≥0∞ := eLpNorm (cylinderFunction 1 (density 1)) (ENNReal.ofReal q) unitHaar +
    ∑' j : ℕ, eLpNorm (densityIncrement (j + 1)) (ENNReal.ofReal q) unitHaar
  have hB : B ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨(memLp_cylinderFunction 1 (density 1) (ENNReal.ofReal q)).eLpNorm_ne_top,
      densityIncrement_eLpNorm_tsum_ne_top q hq1 hq2⟩
  have hb (n : ℕ) :
      eLpNorm (unitDensityL1 n) (ENNReal.ofReal q) unitHaar ≤ B := by
    have hae : (fun x => unitDensityL1 n x) =ᵐ[unitHaar]
        cylinderFunction (n + 1) (density (n + 1)) :=
      (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).coeFn_toL1
    rw [eLpNorm_congr_ae hae]
    exact (finite_density_eLpNorm_le (ENNReal.ofReal q) hp n).trans
      (add_le_add le_rfl (ENNReal.sum_le_tsum (Finset.range n)))
  have hlim := tendstoInMeasure_of_tendsto_Lp unitDensityLimit_tendsto
  have hf : eLpNorm unitDensityFunction (ENNReal.ofReal q) unitHaar ≤ B :=
    eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb) hlim
      (fun n => Lp.aestronglyMeasurable (unitDensityL1 n))
  exact ⟨unitDensityFunction_integrable.aestronglyMeasurable, hf.trans_lt hB.lt_top⟩

theorem unitDensityFunction_memLp_below_two (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q < 2) :
    MemLp unitDensityFunction (ENNReal.ofReal q) unitHaar := by
  rcases hq1.eq_or_lt with hq | hq
  · subst q
    simpa using (memLp_one_iff_integrable.mpr unitDensityFunction_integrable)
  · exact unitDensityFunction_memLp_subcritical q hq hq2

theorem unitDensityFunction_not_memLp_two : ¬ MemLp unitDensityFunction 2 unitHaar :=
  model_not_memLp_two unitDensityFunction unitDensityFunction_integrable
    unitDensityFunction_nonneg rfl

/-- Complete strong-Lq spectrum for real q >= 1. -/
theorem unitDensityFunction_memLp_iff (q : ℝ) (hq : 1 ≤ q) :
    MemLp unitDensityFunction (ENNReal.ofReal q) unitHaar ↔ q < 2 := by
  constructor
  · intro h
    by_contra hq2
    have h2q : (2 : ℝ) ≤ q := le_of_not_gt hq2
    apply unitDensityFunction_not_memLp_two
    apply h.mono_exponent
    simpa using ENNReal.ofReal_le_ofReal h2q
  · exact unitDensityFunction_memLp_below_two q hq

/-- The actual critical exponent is 2. No subcritical integrability or
energy estimate appears as a hypothesis of this theorem. -/
theorem unitDensityFunction_critical_exponent_two :
    IsLUB {q : ℝ | 1 ≤ q ∧ MemLp unitDensityFunction (ENNReal.ofReal q) unitHaar} 2 :=
  lp_critical_exponent_is_two unitDensityFunction_memLp_below_two
    unitDensityFunction_not_memLp_two

end SyracuseReport
