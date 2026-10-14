import DensityRegularity
import Mathlib.Algebra.Group.Units.Equiv

/-! Exact unit-offset relabelling of finite laws and Haar densities. -/
namespace SyracuseReport
open MeasureTheory
open scoped Topology ENNReal
noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def unitResidue (u : (PadicInt 3)ˣ) (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  Units.map (PadicInt.toZModPow n).toMonoidHom u

theorem pmf_map_equiv_apply {X : Type*} (p : PMF X) (e : X ≃ X) (x : X) :
    p.map e x = p (e.symm x) := by
  classical
  rw [PMF.map_apply]
  have hiff (z : X) : x = e z ↔ z = e.symm x := by
    constructor
    · intro h
      apply e.injective
      rw [e.apply_symm_apply]
      exact h.symm
    · intro h; rw [h, e.apply_symm_apply]
  simp_rw [hiff]
  simp

noncomputable def offsetLaw (u : (PadicInt 3)ˣ) (n : ℕ) : PMF (ZMod (3 ^ n)) :=
  (syracuseLaw n).map (unitResidue u n).mulLeft

theorem offsetLaw_apply (u : (PadicInt 3)ˣ) (n : ℕ) (r : ZMod (3 ^ n)) :
    offsetLaw u n r = syracuseLaw n ((unitResidue u n).mulLeft.symm r) :=
  pmf_map_equiv_apply (syracuseLaw n) (unitResidue u n).mulLeft r

theorem offset_atom_floor (u : (PadicInt 3)ˣ) (c : ℝ) (hf : FloorAt c)
    (n : ℕ) (hn : 1 ≤ n) (r : ZMod (3 ^ n)) (hr : IsUnit r) :
    c / (3 : ℝ) ^ n ≤ (offsetLaw u n r).toReal := by
  rw [offsetLaw_apply]
  apply hf n hn
  change IsUnit (((unitResidue u n)⁻¹ : (ZMod (3 ^ n))ˣ) * r)
  exact ((unitResidue u n)⁻¹).isUnit.mul hr

noncomputable def offsetLeastAtom (u : (PadicInt 3)ˣ) (n : ℕ) : ℝ :=
  sInf (Set.range (fun r : (ZMod (3 ^ (n + 1)))ˣ =>
    (offsetLaw u (n + 1) (r : ZMod (3 ^ (n + 1)))).toReal))

theorem offsetLeastAtom_eq (u : (PadicInt 3)ˣ) (n : ℕ) :
    offsetLeastAtom u n = leastAtom n := by
  have hrange : Set.range (fun r : (ZMod (3 ^ (n + 1)))ˣ =>
      (offsetLaw u (n + 1) (r : ZMod (3 ^ (n + 1)))).toReal) =
      Set.range (fun r : (ZMod (3 ^ (n + 1)))ˣ =>
        (syracuseLaw (n + 1) (r : ZMod (3 ^ (n + 1)))).toReal) := by
    ext t
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨(unitResidue u (n + 1))⁻¹ * r, ?_⟩
      simp [offsetLaw_apply, Units.mulLeft]
    · rintro ⟨r, rfl⟩
      refine ⟨unitResidue u (n + 1) * r, ?_⟩
      simp [offsetLaw_apply, Units.mulLeft, ← mul_assoc]
  unfold offsetLeastAtom leastAtom
  rw [hrange]

theorem unit_mul_preimage_cylinder (u : (PadicInt 3)ˣ) (n : ℕ) (r : ZMod (3 ^ n)) :
    (fun x : PadicInt 3 => (u : PadicInt 3) * x) ⁻¹' cylinder n r =
      cylinder n ((unitResidue u n).mulLeft.symm r) := by
  ext x
  change PadicInt.toZModPow n ((u : PadicInt 3) * x) = r ↔ _
  rw [map_mul]
  change (unitResidue u n).mulLeft (PadicInt.toZModPow n x) = r ↔
    PadicInt.toZModPow n x = (unitResidue u n).mulLeft.symm r
  exact (unitResidue u n).mulLeft.apply_eq_iff_eq_symm_apply

theorem unit_mul_measurePreserving (u : (PadicInt 3)ˣ) :
    MeasurePreserving (fun x : PadicInt 3 => (u : PadicInt 3) * x) unitHaar unitHaar := by
  classical
  have hm : Measurable (fun x : PadicInt 3 => (u : PadicInt 3) * x) :=
    (continuous_const.mul continuous_id).measurable
  refine ⟨hm, ?_⟩
  apply measure_eq_of_cylinders
  · intro n r
    rw [Measure.map_apply hm (measurableSet_cylinder n r), unit_mul_preimage_cylinder]
    by_cases hn : 1 ≤ n
    · have hu : IsUnit ((unitResidue u n).mulLeft.symm r) ↔ IsUnit r := by
        change IsUnit (((unitResidue u n)⁻¹ : (ZMod (3 ^ n))ˣ) * r) ↔ IsUnit r
        constructor
        · intro h
          have h' := (unitResidue u n).isUnit.mul h
          simpa [← mul_assoc] using h'
        · intro h
          exact ((unitResidue u n)⁻¹).isUnit.mul h
      simp only [unitHaar_cylinder n hn, hu]
    · have hn0 : n = 0 := by omega
      subst n
      rw [cylinder_zero, cylinder_zero]
  · rw [Measure.map_apply hm MeasurableSet.univ]
    simp

theorem offset_memLp_iff (u : (PadicInt 3)ˣ) (f : PadicInt 3 → ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => f ((u⁻¹ : (PadicInt 3)ˣ) * x)) p unitHaar ↔ MemLp f p unitHaar := by
  constructor
  · intro hf
    have h := hf.comp_measurePreserving (unit_mul_measurePreserving u)
    simpa [Function.comp_def, ← mul_assoc] using h
  · intro hf
    exact hf.comp_measurePreserving (unit_mul_measurePreserving u⁻¹)

noncomputable def unitMulHomeomorph (u : (PadicInt 3)ˣ) : PadicInt 3 ≃ₜ PadicInt 3 where
  toEquiv := u.mulLeft
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem offset_lower_ae_iff (u : (PadicInt 3)ˣ) (f : PadicInt 3 → ℝ) (a : ℝ) :
    (∀ᵐ x ∂unitHaar, a ≤ f ((u⁻¹ : (PadicInt 3)ˣ) * x)) ↔
      ∀ᵐ x ∂unitHaar, a ≤ f x := by
  constructor
  · intro h
    have h' := (unit_mul_measurePreserving u).quasiMeasurePreserving.ae h
    simpa [← mul_assoc] using h'
  · intro h
    exact (unit_mul_measurePreserving u⁻¹).quasiMeasurePreserving.ae h

theorem offset_essInf_eq (u : (PadicInt 3)ˣ) (f : PadicInt 3 → ℝ) :
    essInf (fun x => f ((u⁻¹ : (PadicInt 3)ˣ) * x)) unitHaar = essInf f unitHaar := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  simpa only [ae_iff, not_le] using offset_lower_ae_iff u f a

noncomputable def offsetDensity (u : (PadicInt 3)ˣ) (x : PadicInt 3) : ℝ :=
  unitDensityFunction ((u⁻¹ : (PadicInt 3)ˣ) * x)

noncomputable def offsetMeasure (u : (PadicInt 3)ˣ) : Measure (PadicInt 3) :=
  Measure.map (fun x => (u : PadicInt 3) * x) unitDensityMeasure

instance offsetMeasure_isProbability (u : (PadicInt 3)ˣ) : IsProbabilityMeasure (offsetMeasure u) := by
  constructor
  rw [offsetMeasure, Measure.map_apply (unit_mul_measurePreserving u).measurable MeasurableSet.univ]
  simp

theorem offsetDensity_integrable (u : (PadicInt 3)ˣ) :
    Integrable (offsetDensity u) unitHaar := by
  apply memLp_one_iff_integrable.mp
  exact (offset_memLp_iff u unitDensityFunction 1).2
    (memLp_one_iff_integrable.mpr unitDensityFunction_integrable)

theorem offsetDensity_nonneg (u : (PadicInt 3)ˣ) : ∀ᵐ x ∂unitHaar, 0 ≤ offsetDensity u x :=
  (unit_mul_measurePreserving u⁻¹).quasiMeasurePreserving.ae unitDensityFunction_nonneg

theorem offsetMeasure_cylinder (u : (PadicInt 3)ˣ) (n : ℕ) (r : ZMod (3 ^ n)) :
    offsetMeasure u (cylinder n r) = offsetLaw u n r := by
  rw [offsetMeasure, Measure.map_apply
    (unit_mul_measurePreserving u).measurable (measurableSet_cylinder n r),
    unit_mul_preimage_cylinder, unitDensityMeasure_cylinder, offsetLaw_apply]

theorem offsetMeasure_density (u : (PadicInt 3)ˣ) :
    offsetMeasure u = unitHaar.withDensity (fun x => ENNReal.ofReal (offsetDensity u x)) := by
  have hcomp : (fun x => offsetDensity u ((u : PadicInt 3) * x)) = unitDensityFunction := by
    funext x
    simp [offsetDensity, ← mul_assoc]
  have hcyl (n : ℕ) (r : ZMod (3 ^ n)) : offsetMeasure u (cylinder n r) =
      unitHaar.withDensity (fun x => ENNReal.ofReal (offsetDensity u x)) (cylinder n r) := by
    rw [offsetMeasure_cylinder, offsetLaw_apply, withDensity_apply _ (measurableSet_cylinder n r),
      ← ofReal_integral_eq_lintegral_ofReal (offsetDensity_integrable u).restrict
        (ae_restrict_of_ae (offsetDensity_nonneg u))]
    have htransport := (unit_mul_measurePreserving u).setIntegral_preimage_emb
      (unitMulHomeomorph u).measurableEmbedding (offsetDensity u) (cylinder n r)
    rw [unit_mul_preimage_cylinder, hcomp] at htransport
    rw [← htransport, model_cylinder_integral unitDensityFunction
      unitDensityFunction_integrable unitDensityFunction_nonneg rfl]
    exact (ENNReal.ofReal_toReal ((syracuseLaw n).apply_ne_top _)).symm
  apply measure_eq_of_cylinders _ _ hcyl
  simpa only [cylinder_zero] using hcyl 0 0

theorem offsetDensity_essInf (u : (PadicInt 3)ˣ) :
    essInf (offsetDensity u) unitHaar = essInf unitDensityFunction unitHaar :=
  offset_essInf_eq u unitDensityFunction

theorem offsetDensity_not_memLp_two (u : (PadicInt 3)ˣ) :
    ¬ MemLp (offsetDensity u) 2 unitHaar := by
  intro h
  have hsource := (offset_memLp_iff u unitDensityFunction 2).1 h
  exact model_not_memLp_two unitDensityFunction unitDensityFunction_integrable
    unitDensityFunction_nonneg rfl hsource

theorem offsetDensity_large_set_positive (u : (PadicInt 3)ˣ) (q : ℕ) (hq : 1 ≤ q)
    (r : ZMod (3 ^ q)) (hr : IsUnit r) (M : ℝ) :
    0 < unitHaar (cylinder q r ∩ {x | M < offsetDensity u x}) := by
  let target : Set (PadicInt 3) := cylinder q r ∩ {x | M < offsetDensity u x}
  have hpre : (fun x : PadicInt 3 => (u : PadicInt 3) * x) ⁻¹' target =
      cylinder q ((unitResidue u q).mulLeft.symm r) ∩ {x | M < unitDensityFunction x} := by
    rw [Set.preimage_inter, unit_mul_preimage_cylinder]
    ext x
    simp [target, offsetDensity, ← mul_assoc]
  have hmeasure : unitHaar target = unitHaar
      ((fun x : PadicInt 3 => (u : PadicInt 3) * x) ⁻¹' target) := by
    conv_lhs => rw [← (unit_mul_measurePreserving u).map_eq]
    exact (unitMulHomeomorph u).measurableEmbedding.map_apply _ _
  rw [show cylinder q r ∩ {x | M < offsetDensity u x} = target by rfl, hmeasure, hpre]
  apply model_density_large_set_positive unitDensityFunction unitDensityFunction_integrable
    unitDensityFunction_nonneg rfl q hq
  change IsUnit (((unitResidue u q)⁻¹ : (ZMod (3 ^ q))ˣ) * r)
  exact ((unitResidue u q)⁻¹).isUnit.mul hr

theorem integer_unit_of_not_three (d : ℤ) (hd : ¬(3 : ℤ) ∣ d) :
    IsUnit (d : PadicInt 3) := by
  apply PadicInt.isUnit_iff.mpr
  apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
  intro h
  exact hd (PadicInt.norm_intCast_lt_one_iff.mp h)

theorem rational_offset_conjugacy (d z : ℚ) (a : ℕ) :
    (3 * (d * z) + d) / (2 : ℚ) ^ a = d * ((3 * z + 1) / (2 : ℚ) ^ a) := by
  ring

end SyracuseReport
