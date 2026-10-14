import DensityRegularity
import Mathlib.Analysis.PSeries

/-! Almost-everywhere local dimension from the actual mixing estimates.
The pointwise convergence input is proved here, not assumed as a density
model or substituted by convergence along a subsequence. -/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def observedDensity (n : ℕ) : PadicInt 3 → ℝ :=
  cylinderFunction (n + 1) (density (n + 1))

theorem observedDensity_integrable (n : ℕ) : Integrable (observedDensity n) unitHaar :=
  integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))

theorem observedDensity_l1_bound (C : ℝ) (hC : 0 ≤ C)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * C / (m : ℝ) ^ 2)
    (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) :
    (∫ x, |observedDensity n x - observedDensity m x| ∂unitHaar) ≤
      C / ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have hordered (j k : ℕ) (hjk : j ≤ k) (hNj : N ≤ j) :
      (∫ x, |observedDensity k x - observedDensity j x| ∂unitHaar) ≤
        C / ((N + 1 : ℕ) : ℝ) ^ 2 := by
    rw [observedDensity, observedDensity,
      integral_abs_density_difference_unitHaar (by omega) (Nat.add_le_add_right hjk 1)]
    have hs := mul_le_mul_of_nonneg_left
      (hmix (k + 1) (j + 1) (by omega) (Nat.add_le_add_right hjk 1))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hden : (((N + 1 : ℕ) : ℝ)) ^ 2 ≤ (((j + 1 : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hNj 1) 2
    have hr := div_le_div_of_nonneg_left hC
      (by positivity : (0 : ℝ) < (((N + 1 : ℕ) : ℝ)) ^ 2) hden
    apply le_trans _ hr
    convert hs using 1 <;> ring
  rcases le_total m n with hmn | hnm
  · exact hordered m n hmn hm
  · have he : (fun x => |observedDensity n x - observedDensity m x|) =
        (fun x => |observedDensity m x - observedDensity n x|) := by
      funext x; exact abs_sub_comm _ _
    rw [he]
    exact hordered n m hnm hn

theorem observedDensity_ae_converges :
    ∀ᵐ x ∂unitHaar, ∃ L : ℝ, Tendsto (fun n => observedDensity n x) atTop (𝓝 L) := by
  obtain ⟨C, hC, hmix⟩ := paper_thm_mixing 2 (by norm_num)
  let B : ℕ → ℝ := fun N => (C + 1) / (((N + 1 : ℕ) : ℝ)) ^ 2
  have hs0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs1 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff 1).2 hs0
  have hsB : Summable B := by
    convert hs1.mul_left (C + 1) using 1
    funext n; dsimp [B]; ring
  apply Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun n => (observedDensity_integrable n).aestronglyMeasurable)
    (p := (1 : ℝ≥0∞)) le_rfl (B := fun N => ENNReal.ofReal (B N)) hsB.tsum_ofReal_ne_top
  intro N n m hn hm
  have hi := (observedDensity_integrable n).sub (observedDensity_integrable m)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply (ENNReal.ofReal_lt_ofReal_iff (show 0 < B N by dsimp [B]; positivity)).mpr
  have hb := observedDensity_l1_bound C hC hmix N n m hn hm
  apply hb.trans_lt
  exact div_lt_div_of_pos_right (by linarith : C < C + 1) (by positivity)

noncomputable def localDimensionRatio (x : PadicInt 3) (n : ℕ) : ℝ :=
  -Real.log (atomMass (n + 1) (PadicInt.toZModPow (n + 1) x)) /
    ((((n + 1 : ℕ) : ℝ)) * Real.log 3)

theorem localDimension_of_density_limit (x : PadicInt 3) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun n => observedDensity n x) atTop (𝓝 L))
    (hpos : ∀ n, 0 < observedDensity n x) :
    Tendsto (localDimensionRatio x) atTop (𝓝 1) := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog := hlim.log hL.ne'
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * Real.log 3) atTop atTop := by
    simpa only [mul_comm] using hn.const_mul_atTop hlog3
  have hnum : Tendsto (fun n => Real.log (2 / 3 : ℝ) - Real.log (observedDensity n x))
      atTop (𝓝 (Real.log (2 / 3 : ℝ) - Real.log L)) := tendsto_const_nhds.sub hlog
  have hratio := hnum.div_atTop hden
  have hsum : Tendsto (fun n => (1 : ℝ) +
      (Real.log (2 / 3 : ℝ) - Real.log (observedDensity n x)) /
        ((((n + 1 : ℕ) : ℝ)) * Real.log 3)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hratio
  convert hsum using 1
  funext n
  have hmass : 0 < atomMass (n + 1) (PadicInt.toZModPow (n + 1) x) := by
    have hd := hpos n
    change 0 < (2 / 3 : ℝ) * (3 : ℝ) ^ (n + 1) *
      atomMass (n + 1) (PadicInt.toZModPow (n + 1) x) at hd
    exact (mul_pos_iff_of_pos_left (by positivity)).mp hd
  have hidentity : Real.log (observedDensity n x) =
      Real.log (2 / 3 : ℝ) + (((n + 1 : ℕ) : ℝ)) * Real.log 3 +
        Real.log (atomMass (n + 1) (PadicInt.toZModPow (n + 1) x)) := by
    change Real.log ((2 / 3 : ℝ) * (3 : ℝ) ^ (n + 1) *
      atomMass (n + 1) (PadicInt.toZModPow (n + 1) x)) = _
    rw [Real.log_mul (by positivity) hmass.ne',
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  unfold localDimensionRatio
  field_simp [hlog3.ne', show (((n + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
  linarith

theorem syracuse_exact_dimension :
    ∀ᵐ x ∂unitDensityMeasure, Tendsto (localDimensionRatio x) atTop (𝓝 1) := by
  obtain ⟨c, hc, hfloor⟩ := atom_floor
  have hH : ∀ᵐ x ∂unitHaar, Tendsto (localDimensionRatio x) atTop (𝓝 1) := by
    filter_upwards [observedDensity_ae_converges, unitHaar_ae_unitRegion]
      with x hx hxU
    obtain ⟨L, hlim⟩ := hx
    have hunit1 : IsUnit (PadicInt.toZModPow 1 x) := by
      have he := congrArg (fun s : Set (PadicInt 3) => x ∈ s) unitRegion_eq_unit_reduction
      exact he.mp hxU
    have hlower (n : ℕ) : (2 / 3 : ℝ) * c ≤ observedDensity n x := by
      have hu : IsUnit (PadicInt.toZModPow (n + 1) x) := by
        apply (residueProjection_isUnit_iff (by omega : 1 ≤ n + 1) (by omega)
          (PadicInt.toZModPow (n + 1) x)).mp
        rw [padic_reduction_comp (by omega : 1 ≤ n + 1) x]
        exact hunit1
      have h := unitMinorant_le_density hfloor (n := n + 1) (by omega)
        (PadicInt.toZModPow (n + 1) x)
      simpa only [unitMinorant, if_pos hu, observedDensity, cylinderFunction] using h
    have hLlower : (2 / 3 : ℝ) * c ≤ L :=
      ge_of_tendsto hlim (Eventually.of_forall hlower)
    have hLpos : 0 < L := (by positivity : (0 : ℝ) < (2 / 3 : ℝ) * c).trans_le hLlower
    exact localDimension_of_density_limit x L hLpos hlim
      (fun n => (by positivity : (0 : ℝ) < (2 / 3 : ℝ) * c).trans_le (hlower n))
  have hμ : unitDensityMeasure ≪ unitHaar := withDensity_absolutelyContinuous _ _
  exact hH.filter_mono hμ.ae_le

end SyracuseReport
