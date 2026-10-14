import HaarReference
import UnitProjection

/-! Haar probability on the units, constructed by restricting normalized
additive Haar measure to the two unit classes modulo three.
-/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

def unitRegion : Set (PadicInt 3) := cylinder 1 1 ∪ cylinder 1 2

theorem measurableSet_unitRegion : MeasurableSet unitRegion :=
  (measurableSet_cylinder 1 1).union (measurableSet_cylinder 1 2)

theorem unitRegion_eq_unit_reduction :
    unitRegion = {x : PadicInt 3 | IsUnit (PadicInt.toZModPow 1 x)} := by
  have h (r : ZMod (3 ^ 1)) : (r = 1 ∨ r = 2) ↔ IsUnit r := by
    rw [isUnit_residue_iff (by decide)]
    constructor
    · rintro (rfl | rfl)
      · simp only [ZMod.val_one_eq_one_mod]; norm_num
      · simp only [ZMod.val_ofNat]; norm_num
    · intro hu
      have hv : r.val < 3 := by simpa using r.val_lt
      have vals : r.val = 1 ∨ r.val = 2 := by omega
      rcases vals with hval | hval
      · left
        calc r = (r.val : ZMod (3 ^ 1)) := (ZMod.natCast_zmod_val r).symm
             _ = 1 := by rw [hval]; norm_num
      · right
        calc r = (r.val : ZMod (3 ^ 1)) := (ZMod.natCast_zmod_val r).symm
             _ = 2 := by rw [hval]; norm_num
  ext x
  exact h (PadicInt.toZModPow 1 x)

theorem cylinder_inter_unitRegion (n : ℕ) (hn : 1 ≤ n) (r : ZMod (3 ^ n)) :
    cylinder n r ∩ unitRegion = if IsUnit r then cylinder n r else ∅ := by
  classical
  have hmem (x : PadicInt 3) (hx : x ∈ cylinder n r) :
      x ∈ unitRegion ↔ IsUnit r := by
    rw [unitRegion_eq_unit_reduction]
    change IsUnit (PadicInt.toZModPow 1 x) ↔ IsUnit r
    change PadicInt.toZModPow n x = r at hx
    rw [← padic_reduction_comp hn x, hx]
    exact residueProjection_isUnit_iff hn (by decide) r
  by_cases hr : IsUnit r
  · rw [if_pos hr]
    exact Set.inter_eq_left.mpr (fun x hx => (hmem x hx).mpr hr)
  · rw [if_neg hr]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hu⟩
    exact hr ((hmem x hx).mp hu)

theorem additiveHaar_unitRegion :
    additiveHaar unitRegion = ENNReal.ofReal (2 / 3 : ℝ) := by
  have hd : Disjoint (cylinder 1 (1 : ZMod (3 ^ 1))) (cylinder 1 2) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change PadicInt.toZModPow 1 x = 1 at hx
    change PadicInt.toZModPow 1 x = 2 at hy
    have h : (1 : ZMod 3) = 2 := hx.symm.trans hy
    exact (by decide : (1 : ZMod 3) ≠ 2) h
  rw [unitRegion, measure_union hd (measurableSet_cylinder 1 2),
    additiveHaar_cylinder, additiveHaar_cylinder]
  simp only [pow_one]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  congr 1
  ring

noncomputable def unitHaar : Measure (PadicInt 3) :=
  ENNReal.ofReal (3 / 2 : ℝ) • additiveHaar.restrict unitRegion

instance unitHaar_isProbabilityMeasure : IsProbabilityMeasure unitHaar := by
  constructor
  simp only [unitHaar, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, additiveHaar_unitRegion]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have h : (3 / 2 : ℝ) * (2 / 3) = 1 := by ring
  rw [h, ENNReal.ofReal_one]

theorem unitHaar_cylinder (n : ℕ) (hn : 1 ≤ n) (r : ZMod (3 ^ n)) :
    unitHaar (cylinder n r) =
      if IsUnit r then ENNReal.ofReal ((3 / 2 : ℝ) / (3 : ℝ) ^ n) else 0 := by
  classical
  simp only [unitHaar, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (measurableSet_cylinder n r), cylinder_inter_unitRegion n hn r]
  by_cases hr : IsUnit r
  · rw [if_pos hr, if_pos hr, additiveHaar_cylinder]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    congr 1
    ring
  · simp only [if_neg hr, measure_empty, mul_zero]

theorem unitHaar_isModel : IsUnitHaar unitHaar :=
  ⟨inferInstance, unitHaar_cylinder⟩

theorem unitHaar_unitRegion_compl : unitHaar unitRegionᶜ = 0 := by
  simp only [unitHaar, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply measurableSet_unitRegion.compl, Set.compl_inter_self]
  simp only [measure_empty, mul_zero]

end SyracuseReport
