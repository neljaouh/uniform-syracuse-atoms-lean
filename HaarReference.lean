import HaarCylinders
import PaperStatements
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure

/-! Construction and finite-cylinder characterization of normalized additive
Haar measure. The measure is constructed here, rather than supplied as an
assumption to the limiting-law argument.
-/
namespace SyracuseReport
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def additiveHaar : Measure (PadicInt 3) :=
  Measure.addHaarMeasure (⊤ : PositiveCompacts (PadicInt 3))

instance additiveHaar_isProbabilityMeasure : IsProbabilityMeasure additiveHaar := by
  constructor
  change Measure.addHaarMeasure (⊤ : PositiveCompacts (PadicInt 3)) Set.univ = 1
  simpa only [PositiveCompacts.coe_top] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts (PadicInt 3))))

instance additiveHaar_isAddLeftInvariant : Measure.IsAddLeftInvariant additiveHaar := by
  unfold additiveHaar
  infer_instance

theorem additiveHaar_cylinder_eq_zero (n : ℕ) (r : ZMod (3 ^ n)) :
    additiveHaar (cylinder n r) = additiveHaar (cylinder n 0) := by
  have hpre : (fun x : PadicInt 3 => (r.val : PadicInt 3) + x) ⁻¹' cylinder n r =
      cylinder n 0 := by
    ext x
    simp [cylinder, map_add, map_natCast]
  have h := measure_preimage_add additiveHaar (r.val : PadicInt 3) (cylinder n r)
  rw [hpre] at h
  exact h.symm

theorem sum_additiveHaar_cylinders (n : ℕ) :
    (∑ r : ZMod (3 ^ n), additiveHaar (cylinder n r)) = 1 := by
  classical
  have h := sum_measure_preimage_singleton (μ := additiveHaar)
    (Finset.univ : Finset (ZMod (3 ^ n)))
    (f := fun x : PadicInt 3 => PadicInt.toZModPow n x)
    (fun r _ => measurableSet_cylinder n r)
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

theorem additiveHaar_cylinder (n : ℕ) (r : ZMod (3 ^ n)) :
    additiveHaar (cylinder n r) = ENNReal.ofReal (1 / (3 : ℝ) ^ n) := by
  classical
  have hsum := sum_additiveHaar_cylinders n
  have hconst : (∑ s : ZMod (3 ^ n), additiveHaar (cylinder n s)) =
      ((3 ^ n : ℕ) : ℝ≥0∞) * additiveHaar (cylinder n 0) := by
    rw [Finset.sum_congr rfl (fun s _ => additiveHaar_cylinder_eq_zero n s)]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hmass := congrArg ENNReal.toReal (hconst.symm.trans hsum)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one,
    Nat.cast_pow, Nat.cast_ofNat] at hmass
  have hr : (additiveHaar (cylinder n r)).toReal = 1 / (3 : ℝ) ^ n := by
    rw [additiveHaar_cylinder_eq_zero n r]
    apply (eq_div_iff (by positivity : (3 : ℝ) ^ n ≠ 0)).2
    simpa only [mul_comm] using hmass
  calc
    additiveHaar (cylinder n r) =
        ENNReal.ofReal (additiveHaar (cylinder n r)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal hr

theorem additiveHaar_isModel : IsAdditiveHaar additiveHaar :=
  ⟨inferInstance, additiveHaar_cylinder⟩

end SyracuseReport
