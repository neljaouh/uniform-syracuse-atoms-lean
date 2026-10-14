import HaarDensitySteps
import UnitHaar
import LawIdentification

/-! The finite Syracuse laws are supported on units. Their normalized
densities have integral one for the probability Haar measure on the units.
-/
namespace SyracuseReport
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem syracuseLaw_one_zero : syracuseLaw 1 0 = 0 := by
  rw [syracuseLaw_eq_syracPMF]
  exact Erdos1135.Tao.syracPMF_one_apply_zero

theorem syracuseLaw_nonunit {n : ℕ} (hn : 1 ≤ n) (r : ZMod (3 ^ n))
    (hr : ¬ IsUnit r) : syracuseLaw n r = 0 := by
  classical
  have hu : ¬ IsUnit (residueProjection hn r) := by
    rw [residueProjection_isUnit_iff hn (by decide)]
    exact hr
  have hz : residueProjection hn r = 0 := by
    apply (ZMod.val_eq_zero _).mp
    have hval : (residueProjection hn r).val % 3 = 0 := by
      by_contra hne
      exact hu ((isUnit_residue_iff (by decide) _).mpr hne)
    have hv : (residueProjection hn r).val < 3 := by
      simpa using (residueProjection hn r).val_lt
    omega
  have hle : syracuseLaw n r ≤
      ∑ z : ZMod (3 ^ n),
        if residueProjection hn z = residueProjection hn r then syracuseLaw n z else 0 := by
    simpa only [if_pos rfl] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun z : ZMod (3 ^ n) =>
          if residueProjection hn z = residueProjection hn r then syracuseLaw n z else 0)
        (fun z _ => bot_le) (Finset.mem_univ r))
  rw [← syracuseLaw_project_atoms hn, hz, syracuseLaw_one_zero] at hle
  exact le_antisymm hle bot_le

theorem density_nonunit {n : ℕ} (hn : 1 ≤ n) (r : ZMod (3 ^ n))
    (hr : ¬ IsUnit r) : density n r = 0 := by
  simp only [density, syracuseLaw_nonunit hn r hr, ENNReal.toReal_zero, mul_zero]

theorem integral_cylinderFunction_unitHaar {n : ℕ} (hn : 1 ≤ n)
    (a : ZMod (3 ^ n) → ℝ) (ha : ∀ r, ¬ IsUnit r → a r = 0) :
    (∫ x, cylinderFunction n a x ∂unitHaar) = (3 / 2 : ℝ) * finiteMean a := by
  classical
  rw [integral_cylinderFunction]
  have hterm (r : ZMod (3 ^ n)) :
      unitHaar.real (cylinder n r) * a r = ((3 / 2 : ℝ) / (3 : ℝ) ^ n) * a r := by
    by_cases hr : IsUnit r
    · simp only [Measure.real, unitHaar_cylinder n hn r, if_pos hr,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) / (3 : ℝ) ^ n)]
    · rw [ha r hr, mul_zero, mul_zero]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  unfold finiteMean
  rw [ZMod.card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem integral_liftedDensity_unitHaar {n : ℕ} (hn : 1 ≤ n) :
    (∫ x, cylinderFunction n (density n) x ∂unitHaar) = 1 := by
  rw [integral_cylinderFunction_unitHaar hn _ (density_nonunit hn), finiteMean_density]
  norm_num

theorem unitDensityStep_cylinder_integral {k q : ℕ} (hk : 1 ≤ k)
    (hkq : k ≤ q) (hq : 1 ≤ q) (r : ZMod (3 ^ k)) :
    (∫ x in cylinder k r, cylinderFunction q (density q) x ∂unitHaar) =
      (syracuseLaw k r).toReal := by
  by_cases hr : IsUnit r
  · have hsub : cylinder k r ⊆ unitRegion := by
      intro x hx
      rw [unitRegion_eq_unit_reduction]
      change IsUnit (PadicInt.toZModPow 1 x)
      change PadicInt.toZModPow k x = r at hx
      rw [← padic_reduction_comp hk x, hx]
      exact (residueProjection_isUnit_iff hk (by omega) r).mpr hr
    have hmeasure : unitHaar.restrict (cylinder k r) =
        ENNReal.ofReal (3 / 2 : ℝ) • additiveHaar.restrict (cylinder k r) := by
      rw [unitHaar, Measure.restrict_smul,
        Measure.restrict_restrict (measurableSet_cylinder k r)]
      rw [Set.inter_eq_left.mpr hsub]
    calc
      (∫ x in cylinder k r, cylinderFunction q (density q) x ∂unitHaar) =
          ∫ x, cylinderFunction q (density q) x ∂unitHaar.restrict (cylinder k r) := rfl
      _ = (3 / 2 : ℝ) *
          ∫ x in cylinder k r, cylinderFunction q (density q) x ∂additiveHaar := by
        rw [hmeasure, integral_smul_measure]
        simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2), smul_eq_mul]
      _ = (3 / 2 : ℝ) * ((2 / 3 : ℝ) * (syracuseLaw k r).toReal) := by
        rw [setIntegral_liftedDensity hkq r]
      _ = _ := by ring
  · have hzero : unitHaar.restrict (cylinder k r) = 0 := by
      rw [unitHaar, Measure.restrict_smul,
        Measure.restrict_restrict (measurableSet_cylinder k r),
        cylinder_inter_unitRegion k hk r]
      simp [hr]
    rw [show (∫ x in cylinder k r, cylinderFunction q (density q) x ∂unitHaar) =
      ∫ x, cylinderFunction q (density q) x ∂unitHaar.restrict (cylinder k r) from rfl,
      hzero, integral_zero_measure]
    have hz := syracuseLaw_nonunit hk r hr
    simp [hz]

theorem integral_abs_density_difference_unitHaar {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∫ x, |cylinderFunction n (density n) x -
      cylinderFunction m (density m) x| ∂unitHaar) =
      (3 / 2 : ℝ) * finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) := by
  have h : (fun x => |cylinderFunction n (density n) x -
        cylinderFunction m (density m) x|) =
      cylinderFunction n (fun r => |density n r - density m (residueProjection hmn r)|) := by
    funext x
    simp only [cylinderFunction, padic_reduction_comp]
  rw [h]
  apply integral_cylinderFunction_unitHaar (hm.trans hmn)
  intro r hr
  have hproj : ¬ IsUnit (residueProjection hmn r) := by
    rw [residueProjection_isUnit_iff hmn hm]
    exact hr
  rw [density_nonunit (hm.trans hmn) r hr,
    density_nonunit hm _ hproj, sub_self, abs_zero]

end SyracuseReport
