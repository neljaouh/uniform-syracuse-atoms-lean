import UnitDensityLimit
import MinimumLimit

/-! Atom floors are exactly the a.e. lower bounds of the limiting density
with respect to unit Haar. The forward direction uses closedness of the
positive cone in L1; the reverse direction integrates over each cylinder.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def unitDensityLimit : Lp ℝ 1 unitHaar :=
  Classical.choose exists_unitDensityL1_limit

theorem unitDensityLimit_tendsto :
    Tendsto unitDensityL1 atTop (𝓝 unitDensityLimit) :=
  Classical.choose_spec exists_unitDensityL1_limit

noncomputable def unitDensityFunction : PadicInt 3 → ℝ := unitDensityLimit

theorem unitDensityFunction_integrable : Integrable unitDensityFunction unitHaar :=
  L1.integrable_coeFn unitDensityLimit

theorem unitDensityFunction_nonneg :
    ∀ᵐ x ∂unitHaar, 0 ≤ unitDensityFunction x :=
  (Lp.coeFn_nonneg unitDensityLimit).mpr
    (unitDensityL1_limit_nonneg unitDensityLimit unitDensityLimit_tendsto)

theorem unitHaar_ae_unitRegion : ∀ᵐ x ∂unitHaar, x ∈ unitRegion := by
  apply ae_mem_iff_measure_eq measurableSet_unitRegion.nullMeasurableSet |>.2
  exact measure_of_measure_compl_eq_zero unitHaar_unitRegion_compl

theorem unitDensity_floor_lower {c : ℝ} (hfloor : FloorAt c) :
    ∀ᵐ x ∂unitHaar, (2 / 3 : ℝ) * c ≤ unitDensityFunction x := by
  let δ : ℝ := (2 / 3 : ℝ) * c
  let b : Lp ℝ 1 unitHaar := (integrable_const δ).toL1 (fun _ => δ)
  have happrox : ∀ n, 0 ≤ n → b ≤ unitDensityL1 n := by
    intro n _
    apply (Lp.coeFn_le b (unitDensityL1 n)).mp
    have hU := unitHaar_ae_unitRegion
    filter_upwards [hU,
      (integrable_const δ).coeFn_toL1,
      (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).coeFn_toL1]
      with x hxU hb hn
    change b x ≤ unitDensityL1 n x
    change b x ≤ (integrable_cylinderFunction unitHaar (n + 1)
      (density (n + 1))).toL1 (cylinderFunction (n + 1) (density (n + 1))) x
    rw [hb, hn]
    have hunit1 : IsUnit (PadicInt.toZModPow 1 x) := by
      have heq := congrArg (fun s : Set (PadicInt 3) => x ∈ s)
        unitRegion_eq_unit_reduction
      exact heq.mp hxU
    have hproj : 1 ≤ n + 1 := by omega
    have hunit : IsUnit (PadicInt.toZModPow (n + 1) x) := by
      apply (residueProjection_isUnit_iff (Q := n + 1) (h := 1)
        hproj (by omega) (PadicInt.toZModPow (n + 1) x)).mp
      rw [padic_reduction_comp hproj x]
      exact hunit1
    have hmin := unitMinorant_le_density hfloor (n := n + 1) (by omega)
      (PadicInt.toZModPow (n + 1) x)
    unfold unitMinorant at hmin
    rw [if_pos hunit] at hmin
    simpa only [δ, cylinderFunction] using hmin
  have hclosed : IsClosed (Set.Ici b) := isClosed_Ici
  have hbound : b ≤ unitDensityLimit :=
    hclosed.mem_of_tendsto unitDensityLimit_tendsto
      (Eventually.of_forall fun n => happrox n (Nat.zero_le n))
  have hbound_ae := (Lp.coeFn_le b unitDensityLimit).mpr hbound
  filter_upwards [hbound_ae, (integrable_const δ).coeFn_toL1] with x h hδ
  rw [hδ] at h
  exact h

theorem unitDensity_floor_of_lower {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂unitHaar, (2 / 3 : ℝ) * c ≤ unitDensityFunction x) : FloorAt c := by
  intro n hn r hr
  have hmass := unitDensityL1_cylinder_integral hn unitDensityLimit
    unitDensityLimit_tendsto r
  have hmono : (2 / 3 : ℝ) * c * unitHaar.real (cylinder n r) ≤
      ∫ x in cylinder n r, unitDensityFunction x ∂unitHaar := by
    calc
      _ = ∫ _ in cylinder n r, (2 / 3 : ℝ) * c ∂unitHaar := by
        rw [setIntegral_const, smul_eq_mul]
        ring
      _ ≤ _ := setIntegral_mono_ae
        ((integrable_const ((2 / 3 : ℝ) * c)).restrict (s := cylinder n r))
        (unitDensityFunction_integrable.restrict (s := cylinder n r))
        hlower
  have hmass' : (∫ x in cylinder n r, unitDensityFunction x ∂unitHaar) =
      (syracuseLaw n r).toReal := by
    simpa only [unitDensityFunction] using hmass
  rw [hmass'] at hmono
  rw [Measure.real, unitHaar_cylinder n hn r, if_pos hr, ENNReal.toReal_ofReal
    (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) / (3 : ℝ) ^ n)] at hmono
  have hscale : c / (3 : ℝ) ^ n =
      (2 / 3 : ℝ) * c * ((3 / 2 : ℝ) / (3 : ℝ) ^ n) := by field_simp
  rw [← hscale] at hmono
  exact hmono

theorem floor_iff_unitDensity_lower {c : ℝ} (hc : 0 < c) :
    FloorAt c ↔ ∀ᵐ x ∂unitHaar, (2 / 3 : ℝ) * c ≤ unitDensityFunction x := by
  exact ⟨unitDensity_floor_lower, unitDensity_floor_of_lower hc⟩

end SyracuseReport
