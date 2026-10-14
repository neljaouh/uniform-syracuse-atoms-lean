import DensityEnergy
import DensitySpikes
import TheoremB
import Mathlib.MeasureTheory.Function.L2Space

/-! Density regularity for every representative of the actual Syracuse law.
The endpoint has no energy, upper-density, or spike hypotheses. -/
namespace SyracuseReport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem model_cylinder_integral (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) (n : ℕ) (r : ZMod (3 ^ n)) :
    (∫ x in cylinder n r, f x ∂unitHaar) = atomMass n r := by
  have h : ENNReal.ofReal (∫ x in cylinder n r, f x ∂unitHaar) =
      syracuseLaw n r := by
    calc
      _ = ∫⁻ x in cylinder n r, ENNReal.ofReal (f x) ∂unitHaar :=
        ofReal_integral_eq_lintegral_ofReal hfi.restrict (ae_restrict_of_ae hpos)
      _ = unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) (cylinder n r) :=
        (withDensity_apply _ (measurableSet_cylinder n r)).symm
      _ = _ := by rw [hmodel, unitDensityMeasure_cylinder]
  have hn : 0 ≤ ∫ x in cylinder n r, f x ∂unitHaar :=
    integral_nonneg_of_ae (ae_restrict_of_ae hpos)
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hn] at hr
  exact hr

theorem cylinderFunction_mul_eq_sum (n : ℕ) (a : ZMod (3 ^ n) → ℝ)
    (f : PadicInt 3 → ℝ) :
    (fun x => cylinderFunction n a x * f x) =
      ∑ r : ZMod (3 ^ n), (cylinder n r).indicator (fun x => a r * f x) := by
  classical
  funext x
  simp [cylinderFunction, cylinder, Set.indicator_apply, eq_comm]

theorem integrable_mul_cylinderFunction (f : PadicInt 3 → ℝ)
    (hf : Integrable f unitHaar) (n : ℕ) (a : ZMod (3 ^ n) → ℝ) :
    Integrable (fun x => cylinderFunction n a x * f x) unitHaar := by
  rw [cylinderFunction_mul_eq_sum]
  exact integrable_finset_sum' Finset.univ (fun r _ =>
    (hf.const_mul (a r)).indicator (measurableSet_cylinder n r))

theorem integral_mul_cylinderFunction (f : PadicInt 3 → ℝ)
    (hf : Integrable f unitHaar) (n : ℕ) (a : ZMod (3 ^ n) → ℝ) :
    (∫ x, cylinderFunction n a x * f x ∂unitHaar) =
      ∑ r : ZMod (3 ^ n), a r * ∫ x in cylinder n r, f x ∂unitHaar := by
  classical
  calc
    _ = ∫ x, ∑ r : ZMod (3 ^ n),
        (cylinder n r).indicator (fun y => a r * f y) x ∂unitHaar := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by
            simp [cylinderFunction, cylinder, Set.indicator_apply, eq_comm])
    _ = ∑ r : ZMod (3 ^ n),
        ∫ x, (cylinder n r).indicator (fun y => a r * f y) x ∂unitHaar :=
          integral_finset_sum Finset.univ (fun r _ =>
            (hf.const_mul (a r)).indicator (measurableSet_cylinder n r))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integral_indicator (measurableSet_cylinder n r), integral_const_mul]

theorem integral_density_sq (n : ℕ) (hn : 1 ≤ n) :
    (∫ x, (cylinderFunction n (density n) x) ^ 2 ∂unitHaar) =
      collisionEnergy n := by
  change (∫ x, cylinderFunction n (fun r => density n r ^ 2) x ∂unitHaar) = _
  rw [integral_cylinderFunction_unitHaar hn _ (fun r hr => by
    rw [density_nonunit hn r hr]; norm_num)]
  unfold finiteMean density collisionEnergy atomMass
  simp only [mul_pow, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  field_simp
  <;> ring

theorem integral_density_mul_model (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) (n : ℕ) :
    (∫ x, cylinderFunction n (density n) x * f x ∂unitHaar) =
      collisionEnergy n := by
  rw [integral_mul_cylinderFunction f hfi]
  simp_rw [model_cylinder_integral f hfi hpos hmodel]
  unfold collisionEnergy density atomMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem collisionEnergy_le_integral_sq (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) (hf2 : MemLp f 2 unitHaar) (n : ℕ) (hn : 1 ≤ n) :
    collisionEnergy n ≤ ∫ x, f x ^ 2 ∂unitHaar := by
  let g := cylinderFunction n (density n)
  have hfsq := hf2.integrable_sq
  have hgf := integrable_mul_cylinderFunction f hfi n (density n)
  change Integrable (fun x => g x * f x) unitHaar at hgf
  have hgsq : Integrable (fun x => g x ^ 2) unitHaar :=
    integrable_cylinderFunction unitHaar n (fun r => density n r ^ 2)
  have hidentity : (fun x => (f x - g x) ^ 2) =
      (fun x => (f x ^ 2 - 2 * (g x * f x)) + g x ^ 2) := by
    funext x
    ring
  have hnonneg : 0 ≤ ∫ x, (f x - g x) ^ 2 ∂unitHaar :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [hidentity] at hnonneg
  have hsplit := integral_add (hfsq.sub (hgf.const_mul 2)) hgsq
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub hfsq (hgf.const_mul 2), integral_const_mul] at hnonneg
  have hcross := integral_density_mul_model f hfi hpos hmodel n
  have henergy := integral_density_sq n hn
  change (∫ x, g x * f x ∂unitHaar) = collisionEnergy n at hcross
  change (∫ x, g x ^ 2 ∂unitHaar) = collisionEnergy n at henergy
  rw [hcross, henergy] at hnonneg
  linarith

theorem model_not_memLp_two (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) : ¬ MemLp f 2 unitHaar := by
  intro hf2
  obtain ⟨c, hc, hfloor⟩ := atom_floor
  obtain ⟨n, hn, hlarge⟩ :=
    collisionEnergy_unbounded hc hfloor (∫ x, f x ^ 2 ∂unitHaar)
  exact (not_lt_of_ge (collisionEnergy_le_integral_sq f hfi hpos hmodel hf2 n hn)) hlarge

theorem model_density_not_bounded_on_cylinder (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) (q : ℕ) (hq : 1 ≤ q) (r : ZMod (3 ^ q))
    (hr : IsUnit r) (M : ℝ) :
    ¬ (∀ᵐ x ∂unitHaar.restrict (cylinder q r), f x ≤ M) := by
  intro hupper
  obtain ⟨n, hqn, s, hs, hproj, hlarge⟩ := large_density_in_cylinder q hq r hr M
  have hsub : cylinder n s ⊆ cylinder q r := by
    intro x hx
    change PadicInt.toZModPow q x = r
    rw [← padic_reduction_comp hqn x]
    change residueProjection hqn (PadicInt.toZModPow n x) = r
    change PadicInt.toZModPow n x = s at hx
    rw [hx, hproj]
  have hupper' : ∀ᵐ x ∂unitHaar.restrict (cylinder n s), f x ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hsub hupper
  have hmono : (∫ x in cylinder n s, f x ∂unitHaar) ≤
      ∫ x in cylinder n s, M ∂unitHaar :=
    integral_mono_ae hfi.restrict (integrable_const M) hupper'
  rw [model_cylinder_integral f hfi hpos hmodel,
    setIntegral_const, smul_eq_mul] at hmono
  have hmass : unitHaar.real (cylinder n s) = (3 / 2 : ℝ) / (3 : ℝ) ^ n := by
    rw [Measure.real, unitHaar_cylinder n (hq.trans hqn) s, if_pos hs,
      ENNReal.toReal_ofReal (by positivity)]
  have hmasspos : 0 < unitHaar.real (cylinder n s) := by rw [hmass]; positivity
  have havg : density n s = atomMass n s / unitHaar.real (cylinder n s) := by
    rw [hmass]
    unfold density atomMass
    field_simp
    <;> ring
  have hbound : density n s ≤ M := by
    rw [havg]
    exact (div_le_iff₀ hmasspos).mpr (by simpa only [mul_comm] using hmono)
  exact (not_lt_of_ge hbound) hlarge

theorem model_density_large_set_positive (f : PadicInt 3 → ℝ)
    (hfi : Integrable f unitHaar) (hpos : ∀ᵐ x ∂unitHaar, 0 ≤ f x)
    (hmodel : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
      unitDensityMeasure) (q : ℕ) (hq : 1 ≤ q) (r : ZMod (3 ^ q))
    (hr : IsUnit r) (M : ℝ) :
    0 < unitHaar (cylinder q r ∩ {x | M < f x}) := by
  have hn := model_density_not_bounded_on_cylinder f hfi hpos hmodel q hq r hr M
  have hne : (unitHaar.restrict (cylinder q r)) {x | M < f x} ≠ 0 := by
    intro hz
    apply hn
    rw [ae_iff]
    simpa only [not_le] using hz
  have hp := bot_lt_iff_ne_bot.mpr hne
  rw [Measure.restrict_apply' (measurableSet_cylinder q r), Set.inter_comm] at hp
  exact hp

theorem no_continuous_representative_of_cylinder_unbounded
    (f : PadicInt 3 → ℝ)
    (hunbounded : ∀ q : ℕ, 1 ≤ q → ∀ r : ZMod (3 ^ q), IsUnit r →
      ∀ M : ℝ, ¬ (∀ᵐ x ∂unitHaar.restrict (cylinder q r), f x ≤ M))
    (V : Set (PadicInt 3)) (hV : IsOpen V) (hne : V.Nonempty)
    (hVU : V ⊆ unitRegion) (g : PadicInt 3 → ℝ) (hg : ContinuousOn g V) :
    ¬ (g =ᵐ[unitHaar.restrict V] f) := by
  intro heq
  obtain ⟨x, hxV⟩ := hne
  obtain ⟨W, ⟨n, r, rfl⟩, hxC, hCV⟩ :=
    cylinderFamily_isTopologicalBasis.exists_subset_of_mem_open hxV hV
  let q := n + 1
  let s := PadicInt.toZModPow q x
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hs : IsUnit s := by
    have hxU := hVU hxV
    rw [unitRegion_eq_unit_reduction] at hxU
    apply (residueProjection_isUnit_iff hq (by decide) s).mp
    simpa only [s, padic_reduction_comp] using hxU
  have hsub : cylinder q s ⊆ V := by
    apply Set.Subset.trans ?_ hCV
    intro y hy
    change PadicInt.toZModPow n y = r
    have hstep : n ≤ q := by dsimp [q]; omega
    rw [← padic_reduction_comp hstep y]
    change PadicInt.toZModPow q y = s at hy
    rw [hy]
    simpa only [s, padic_reduction_comp] using hxC
  have hcompact : IsCompact (cylinder q s) :=
    (isClopen_cylinder q s).isClosed.isCompact
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image (hg.mono hsub)
  apply hunbounded q hq s hs M
  have heq' := ae_restrict_of_ae_restrict_of_subset hsub heq
  filter_upwards [heq', ae_restrict_mem (measurableSet_cylinder q s)] with y hy hyC
  rw [← hy]
  exact hM (Set.mem_image_of_mem g hyC)

/-- Exact core statement of Theorem B-prime. The energy and regularity
conclusions have only the data already specified by Theorems A and B. -/
def DensityRegularityStatement : Prop :=
  (∀ ell : ℝ, 0 < ell → Tendsto normalizedMinimum atTop (𝓝 ell) →
    ∀ n : ℕ, 1 ≤ n →
      10 / 9 + (4 * ell / 9) * ((n - 1 : ℕ) : ℝ) ≤ collisionEnergy n) ∧
  ∀ (μ H : Measure (PadicInt 3)) (f : PadicInt 3 → ℝ),
    IsSyracuseLimit μ → IsUnitHaar H →
    Integrable f H → (∀ᵐ x ∂H, 0 ≤ f x) →
    μ = H.withDensity (fun x => ENNReal.ofReal (f x)) →
      (¬ MemLp f 2 H) ∧
      (∀ q : ℕ, 1 ≤ q → ∀ r : ZMod (3 ^ q), IsUnit r →
        ∀ M : ℝ, 0 < H (cylinder q r ∩ {x | M < f x})) ∧
      ∀ V : Set (PadicInt 3), IsOpen V → V.Nonempty → V ⊆ unitRegion →
        ∀ g : PadicInt 3 → ℝ, ContinuousOn g V → ¬ (g =ᵐ[H.restrict V] f)

theorem main_density_regularity : DensityRegularityStatement := by
  constructor
  · intro ell hell hlim n hn
    exact collisionEnergy_linear
      (floor_of_positive_normalizedMinimum_limit hell hlim) n hn
  · intro μ H f hμ hH hfi hpos hmodel
    have hH' := unitHaar_unique H hH
    subst H
    have hm : unitHaar.withDensity (fun x => ENNReal.ofReal (f x)) =
        unitDensityMeasure := hmodel.symm.trans (unitDensityMeasure_unique μ hμ)
    refine ⟨model_not_memLp_two f hfi hpos hm, ?_, ?_⟩
    · exact fun q hq r hr M => model_density_large_set_positive f hfi hpos hm q hq r hr M
    · exact no_continuous_representative_of_cylinder_unbounded f
        (fun q hq r hr M => model_density_not_bounded_on_cylinder f hfi hpos hm q hq r hr M)

#check main_density_regularity

end SyracuseReport
