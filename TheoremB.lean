import UnitDensityModel
import AtomFloorBridge

/-! The constructed unit-Haar density satisfies the paper's floor
equivalence. Combining that equivalence with the least-atom limit gives the
optimal essential lower bound and Theorem B.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem floor_of_unitDensity_model {f : PadicInt 3 → ℝ}
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂unitHaar, (2 / 3 : ℝ) * c ≤ f x) : FloorAt c := by
  intro n hn r hr
  have hmass :
      ENNReal.ofReal (∫ x in cylinder n r, f x ∂unitHaar) =
        syracuseLaw n r := by
    calc
      ENNReal.ofReal (∫ x in cylinder n r, f x ∂unitHaar) =
          ∫⁻ x in cylinder n r, ENNReal.ofReal (f x) ∂unitHaar :=
        ofReal_integral_eq_lintegral_ofReal
          (hfi.restrict (s := cylinder n r))
          (ae_restrict_of_ae hpos)
      _ = unitHaar.withDensity (fun x => ENNReal.ofReal (f x))
          (cylinder n r) := (withDensity_apply _ (measurableSet_cylinder n r)).symm
      _ = unitDensityMeasure (cylinder n r) := congrArg (fun M => M (cylinder n r)) hmodel
      _ = syracuseLaw n r := unitDensityMeasure_cylinder n r
  have hmono : (2 / 3 : ℝ) * c * unitHaar.real (cylinder n r) ≤
      ∫ x in cylinder n r, f x ∂unitHaar := by
    calc
      _ = ∫ _ in cylinder n r, (2 / 3 : ℝ) * c ∂unitHaar := by
        rw [setIntegral_const, smul_eq_mul]
        ring
      _ ≤ _ := setIntegral_mono_ae
        ((integrable_const ((2 / 3 : ℝ) * c)).restrict (s := cylinder n r))
        (hfi.restrict (s := cylinder n r)) hlower
  have hnonneg : 0 ≤ ∫ x in cylinder n r, f x ∂unitHaar :=
    le_trans (by positivity) hmono
  have hreal : (∫ x in cylinder n r, f x ∂unitHaar) = (syracuseLaw n r).toReal := by
    have ht := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_ofReal hnonneg] at ht
    exact ht
  rw [Measure.real, unitHaar_cylinder n hn r, if_pos hr, ENNReal.toReal_ofReal
    (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) / (3 : ℝ) ^ n)] at hmono
  rw [hreal] at hmono
  have hscale : c / (3 : ℝ) ^ n =
      (2 / 3 : ℝ) * c * ((3 / 2 : ℝ) / (3 : ℝ) ^ n) := by field_simp
  rw [← hscale] at hmono
  exact hmono

theorem paper_prop_haar : PaperStatements.prop_haar := by
  intro μ H hμ hH c hc
  have hμmodel := unitDensityMeasure_unique μ hμ
  have hHmodel := unitHaar_unique H hH
  constructor
  · intro hfloor
    refine ⟨unitDensityFunction, ?_, ?_, ?_, ?_⟩
    · simpa [hHmodel] using unitDensityFunction_integrable
    · simpa [hHmodel] using unitDensityFunction_nonneg
    · calc
        μ = unitDensityMeasure := hμmodel
        _ = unitHaar.withDensity (fun x => ENNReal.ofReal (unitDensityFunction x)) := rfl
        _ = H.withDensity (fun x => ENNReal.ofReal (unitDensityFunction x)) :=
          congrArg (fun M : Measure (PadicInt 3) =>
            M.withDensity (fun x => ENNReal.ofReal (unitDensityFunction x))) hHmodel.symm
    · simpa [hHmodel] using unitDensity_floor_lower hfloor
  · rintro ⟨f, hfi, hfn, hμf, hlower⟩
    have hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
        unitDensityMeasure := by
      calc
        unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
            H.withDensity (fun x => ENNReal.ofReal (f x)) :=
          congrArg (fun M : Measure (PadicInt 3) => M.withDensity (fun x => ENNReal.ofReal (f x)))
            hHmodel.symm
        _ = μ := hμf.symm
        _ = unitDensityMeasure := hμmodel
    have hfiU : Integrable f unitHaar := by simpa [hHmodel] using hfi
    have hposU : ∀ᵐ x ∂unitHaar, 0 ≤ f x := by simpa [hHmodel] using hfn
    have hlowerU : ∀ᵐ x ∂unitHaar, (2 / 3 : ℝ) * c ≤ f x := by
      simpa [hHmodel] using hlower
    exact floor_of_unitDensity_model hfiU hposU hmodel hc hlowerU

theorem unitHaar_absolutelyContinuous_of_positive_density
    {μ : Measure (PadicInt 3)} {f : PadicInt 3 → ℝ} (hmodel : μ =
      unitHaar.withDensity (fun x => ENNReal.ofReal (f x))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ᵐ x ∂unitHaar, δ ≤ f x) : unitHaar ≪ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_
  rw [hmodel, withDensity_apply _ hs] at hμs
  have hlin : ENNReal.ofReal δ * unitHaar s ≤
      ∫⁻ x in s, ENNReal.ofReal (f x) ∂unitHaar := by
    calc
      ENNReal.ofReal δ * unitHaar s = ∫⁻ _ in s, ENNReal.ofReal δ ∂unitHaar :=
        (setLIntegral_const s (ENNReal.ofReal δ)).symm
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hlower] with x hx
        exact ENNReal.ofReal_le_ofReal hx
  rw [hμs] at hlin
  have hzero : ENNReal.ofReal δ * unitHaar s = 0 := le_antisymm hlin bot_le
  rcases mul_eq_zero.mp hzero with hδzero | hszero
  · exact False.elim ((ENNReal.ofReal_ne_zero_iff.mpr hδ) hδzero)
  · exact hszero

set_option maxHeartbeats 0 in
theorem unitDensityFunction_essInf (ell : ℝ) (hell : 0 < ell)
    (hlim : Tendsto normalizedMinimum atTop (𝓝 ell)) :
    essInf unitDensityFunction unitHaar = (2 / 3 : ℝ) * ell := by
  have hfloor : FloorAt ell := floor_of_positive_normalizedMinimum_limit hell hlim
  have hlower := unitDensity_floor_lower hfloor
  rw [essInf_eq_sSup]
  apply IsGreatest.csSup_eq
  constructor
  · have h := (ae_iff).mp hlower
    simpa only [not_le] using h
  · intro a ha
    by_cases hle' : a ≤ (2 / 3 : ℝ) * ell
    · exact hle'
    have hgt : (2 / 3 : ℝ) * ell < a := lt_of_not_ge hle'
    have haPos : 0 < a := by nlinarith
    have hae : ∀ᵐ x ∂unitHaar, a ≤ unitDensityFunction x := by
      rw [ae_iff]
      simpa only [not_le] using ha
    have hc : 0 < (3 / 2 : ℝ) * a := by positivity
    have hfloorA : FloorAt ((3 / 2 : ℝ) * a) :=
      (floor_iff_unitDensity_lower hc).2 (by
        filter_upwards [hae] with x hx
        nlinarith)
    have hminor : ∀ n, (3 / 2 : ℝ) * a ≤ normalizedMinimum n :=
      fun n => normalizedMinimum_lower_of_floor hfloorA n
    have hlimle : (3 / 2 : ℝ) * a ≤ ell :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun n => hminor n)
    nlinarith

theorem main_theorem_B : MainTheoremB := by
  obtain ⟨_, _, ell, hell, _, hlim, _, _⟩ := main_theorem_A
  have hfloor : FloorAt ell := floor_of_positive_normalizedMinimum_limit hell hlim
  have hlower := unitDensity_floor_lower hfloor
  refine ⟨unitDensityMeasure, unitHaar, unitDensityFunction, ell,
    unitDensityMeasure_isSyracuseLimit, unitHaar_isModel, hell, hlim,
    unitDensityFunction_integrable, unitDensityFunction_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact unitDensityFunction_essInf ell hell hlim
  · exact withDensity_absolutelyContinuous unitHaar
      (fun x => ENNReal.ofReal (unitDensityFunction x))
  · exact unitHaar_absolutelyContinuous_of_positive_density rfl
      (by positivity : 0 < (2 / 3 : ℝ) * ell) hlower
  · exact fun c hc => floor_iff_unitDensity_lower hc

end SyracuseReport
