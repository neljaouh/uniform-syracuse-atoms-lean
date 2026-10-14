import HaarReference
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Finite-quotient observables as integrable functions on the p-adic integers.
The normalized Haar integral is exactly the finite arithmetic mean, so the
finite mixing theorem applies to the lifted densities in L1.
-/
namespace SyracuseReport
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def cylinderFunction (n : ℕ) (a : ZMod (3 ^ n) → ℝ) : PadicInt 3 → ℝ :=
  fun x => a (PadicInt.toZModPow n x)

theorem cylinderFunction_eq_sum (n : ℕ) (a : ZMod (3 ^ n) → ℝ) :
    cylinderFunction n a =
      ∑ r : ZMod (3 ^ n), (cylinder n r).indicator (fun _ => a r) := by
  classical
  funext x
  simp [cylinderFunction, cylinder, Set.indicator_apply, eq_comm]

theorem integrable_cylinderFunction (μ : Measure (PadicInt 3)) [IsFiniteMeasure μ]
    (n : ℕ) (a : ZMod (3 ^ n) → ℝ) : Integrable (cylinderFunction n a) μ := by
  classical
  rw [cylinderFunction_eq_sum]
  exact integrable_finset_sum' Finset.univ (fun r _ =>
    (integrable_const (a r)).indicator (measurableSet_cylinder n r))

theorem integral_cylinderFunction (μ : Measure (PadicInt 3)) [IsFiniteMeasure μ]
    (n : ℕ) (a : ZMod (3 ^ n) → ℝ) :
    (∫ x, cylinderFunction n a x ∂μ) =
      ∑ r : ZMod (3 ^ n), μ.real (cylinder n r) * a r := by
  classical
  rw [cylinderFunction_eq_sum]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum Finset.univ (fun r _ =>
    (integrable_const (a r)).indicator (measurableSet_cylinder n r))]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_indicator_const (a r) (measurableSet_cylinder n r)

theorem integral_cylinderFunction_additiveHaar (n : ℕ) (a : ZMod (3 ^ n) → ℝ) :
    (∫ x, cylinderFunction n a x ∂additiveHaar) = finiteMean a := by
  classical
  rw [integral_cylinderFunction]
  simp only [Measure.real, additiveHaar_cylinder,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (3 : ℝ) ^ n)]
  rw [← Finset.mul_sum]
  unfold finiteMean
  rw [ZMod.card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem integral_liftedDensity (n : ℕ) :
    (∫ x, cylinderFunction n (density n) x ∂additiveHaar) = 2 / 3 := by
  rw [integral_cylinderFunction_additiveHaar, finiteMean_density]

theorem setIntegral_liftedDensity {k n : ℕ} (hkn : k ≤ n) (r : ZMod (3 ^ k)) :
    (∫ x in cylinder k r, cylinderFunction n (density n) x ∂additiveHaar) =
      (2 / 3 : ℝ) * (syracuseLaw k r).toReal := by
  classical
  rw [integral_cylinderFunction]
  have hterm (z : ZMod (3 ^ n)) :
      (additiveHaar.restrict (cylinder k r)).real (cylinder n z) * density n z =
        (2 / 3 : ℝ) *
          (if residueProjection hkn z = r then (syracuseLaw n z).toReal else 0) := by
    rw [Measure.real, Measure.restrict_apply (measurableSet_cylinder n z),
      Set.inter_comm, cylinder_inter_of_le hkn]
    by_cases hz : residueProjection hkn z = r
    · rw [if_pos hz, if_pos hz, additiveHaar_cylinder,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (3 : ℝ) ^ n)]
      unfold density
      field_simp
    · simp only [if_neg hz, measure_empty, ENNReal.toReal_zero, zero_mul, mul_zero]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← syracuseLaw_project_real hkn r]

theorem integral_abs_density_difference {m n : ℕ} (hmn : m ≤ n) :
    (∫ x, |cylinderFunction n (density n) x -
      cylinderFunction m (density m) x| ∂additiveHaar) =
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) := by
  have h : (fun x => |cylinderFunction n (density n) x -
        cylinderFunction m (density m) x|) =
      cylinderFunction n (fun r => |density n r - density m (residueProjection hmn r)|) := by
    funext x
    simp only [cylinderFunction, padic_reduction_comp]
  rw [h, integral_cylinderFunction_additiveHaar]

end SyracuseReport
