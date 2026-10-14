import UnitDensityFloor
import Stationarity

/-! The unit-Haar L1 limit represents the Syracuse probability itself. Thus
the cylinder-integral formula also identifies the measure defined by its
density on every measurable set.
-/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def unitDensityMeasure : Measure (PadicInt 3) :=
  unitHaar.withDensity (fun x => ENNReal.ofReal (unitDensityFunction x))

theorem unitDensityMeasure_cylinder (n : ℕ) (r : ZMod (3 ^ n)) :
    unitDensityMeasure (cylinder n r) = syracuseLaw n r := by
  by_cases hn : 1 ≤ n
  · rw [unitDensityMeasure, withDensity_apply (fun x => ENNReal.ofReal
      (unitDensityFunction x)) (measurableSet_cylinder n r),
      ← ofReal_integral_eq_lintegral_ofReal
        (unitDensityFunction_integrable.restrict (s := cylinder n r))
        (ae_restrict_of_ae unitDensityFunction_nonneg)]
    have hi := unitDensityL1_cylinder_integral hn unitDensityLimit unitDensityLimit_tendsto r
    have hi' : (∫ x in cylinder n r, unitDensityFunction x ∂unitHaar) =
        (syracuseLaw n r).toReal := by
      simpa only [unitDensityFunction] using hi
    rw [hi']
    exact ENNReal.ofReal_toReal ((syracuseLaw n).apply_ne_top r)
  · have hn0 : n = 0 := by omega
    subst n
    have hr : r = 0 := by
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    subst r
    have hcyl : cylinder 0 (0 : ZMod (3 ^ 0)) = Set.univ := by
      ext x
      simp only [cylinder, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    rw [unitDensityMeasure, hcyl, withDensity_apply (fun x => ENNReal.ofReal
        (unitDensityFunction x)) MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal unitDensityFunction_integrable
        unitDensityFunction_nonneg]
    have hi := unitDensityL1_limit_integral unitDensityLimit unitDensityLimit_tendsto
    have hi' : (∫ x, unitDensityFunction x ∂unitHaar) = 1 := by
      simpa only [unitDensityFunction] using hi
    rw [hi']
    simp [syracuseLaw]

instance unitDensityMeasure_isProbability : IsProbabilityMeasure unitDensityMeasure := by
  constructor
  have h := unitDensityMeasure_cylinder 0 (0 : ZMod (3 ^ 0))
  have hcyl : cylinder 0 (0 : ZMod (3 ^ 0)) = Set.univ := by
    ext x
    simp only [cylinder, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    change (_ : ZMod 1) = _
    exact Subsingleton.elim _ _
  rw [hcyl] at h
  simpa [syracuseLaw] using h

theorem unitDensityMeasure_isSyracuseLimit : IsSyracuseLimit unitDensityMeasure :=
  ⟨inferInstance, unitDensityMeasure_cylinder⟩

theorem unitDensityMeasure_unique (μ : Measure (PadicInt 3))
    (hμ : IsSyracuseLimit μ) : μ = unitDensityMeasure := by
  letI := hμ.1
  exact measure_eq_of_cylinders μ unitDensityMeasure
    (fun n r => (hμ.2 n r).trans (unitDensityMeasure_cylinder n r).symm)
    (by rw [measure_univ, measure_univ])

theorem unitHaar_unique (H : Measure (PadicInt 3)) (hH : IsUnitHaar H) : H = unitHaar := by
  letI := hH.1
  apply measure_eq_of_cylinders H unitHaar
  · intro n
    cases n with
    | zero =>
      intro r
      have hr : r = 0 := by
        change (_ : ZMod 1) = _
        exact Subsingleton.elim _ _
      subst r
      have hcyl : cylinder 0 (0 : ZMod (3 ^ 0)) = Set.univ := by
        ext x
        simp only [cylinder, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        change (_ : ZMod 1) = _
        exact Subsingleton.elim _ _
      simpa only [hcyl, measure_univ]
    | succ n =>
      intro r
      exact (hH.2 (n + 1) (by omega) r).trans (unitHaar_cylinder (n + 1) (by omega) r).symm
  · simp [measure_univ]

end SyracuseReport
