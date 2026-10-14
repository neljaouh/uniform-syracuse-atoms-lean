import UnitDensitySteps
import MixingBridge
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpOrder

/-! The normalized finite densities are Cauchy in L1 of unit Haar. Their
limit inherits every cylinder integral, which is the finite-level input to
the optimal atom-floor equivalence.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def unitDensityL1 (n : ℕ) : Lp ℝ 1 unitHaar :=
  (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).toL1
    (cylinderFunction (n + 1) (density (n + 1)))

theorem unitDensityL1_dist (n m : ℕ) :
    dist (unitDensityL1 n) (unitDensityL1 m) =
      ∫ x, |cylinderFunction (n + 1) (density (n + 1)) x -
        cylinderFunction (m + 1) (density (m + 1)) x| ∂unitHaar := by
  rw [dist_eq_norm]
  unfold unitDensityL1
  rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

theorem unitDensityL1_cauchy : CauchySeq unitDensityL1 := by
  obtain ⟨C, _hC, hmix⟩ := paper_thm_mixing 1 (by decide)
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (0 : ℝ) (C / ε))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hprod : C < ε * (N : ℝ) := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
    nlinarith
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
  have hratio : C / (N + 1 : ℕ) < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (N + 1 : ℕ))).mpr
    rw [hcast]
    nlinarith
  refine ⟨N, ?_⟩
  intro n hn
  rw [unitDensityL1_dist]
  have hb := integral_abs_density_difference_unitHaar
    (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)) (Nat.add_le_add_right hn 1)
  have hmixed := hmix (n + 1) (N + 1) (by omega) (Nat.add_le_add_right hn 1)
  have hscaled := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hnorm :
      ∫ x, |cylinderFunction (n + 1) (density (n + 1)) x -
        cylinderFunction (N + 1) (density (N + 1)) x| ∂unitHaar =
        (3 / 2 : ℝ) * finiteMean (fun r : ZMod (3 ^ (n + 1)) =>
          |density (n + 1) r - density (N + 1) (residueProjection
            (Nat.add_le_add_right hn 1) r)|) := hb
  rw [hnorm]
  have hfinal : (3 / 2 : ℝ) * ((2 / 3 : ℝ) * C / ((N : ℝ) + 1)) < ε := by
    calc
      (3 / 2 : ℝ) * ((2 / 3 : ℝ) * C / ((N : ℝ) + 1)) = C / ((N : ℝ) + 1) := by ring
      _ < ε := by simpa only [hcast] using hratio
  have hscaled' : (3 / 2 : ℝ) * finiteMean (fun r : ZMod (3 ^ (n + 1)) =>
      |density (n + 1) r - density (N + 1) (residueProjection
        (Nat.add_le_add_right hn 1) r)|) ≤
      (3 / 2 : ℝ) * ((2 / 3 : ℝ) * C / ((N : ℝ) + 1)) := by
    simpa only [pow_one, hcast] using hscaled
  exact hscaled'.trans_lt hfinal

theorem exists_unitDensityL1_limit :
    ∃ f : Lp ℝ 1 unitHaar, Tendsto unitDensityL1 atTop (𝓝 f) :=
  cauchySeq_tendsto_of_complete unitDensityL1_cauchy

theorem unitDensityL1_integral (n : ℕ) :
    (∫ x, unitDensityL1 n x ∂unitHaar) = 1 := by
  calc
    (∫ x, unitDensityL1 n x ∂unitHaar) =
        ∫ x, cylinderFunction (n + 1) (density (n + 1)) x ∂unitHaar :=
      integral_congr_ae (integrable_cylinderFunction unitHaar (n + 1)
        (density (n + 1))).coeFn_toL1
    _ = 1 := integral_liftedDensity_unitHaar (by omega)

theorem unitDensityL1_limit_integral (f : Lp ℝ 1 unitHaar)
    (hf : Tendsto unitDensityL1 atTop (𝓝 f)) : (∫ x, f x ∂unitHaar) = 1 := by
  have hlim := (continuous_setIntegral (μ := unitHaar) (E := ℝ) Set.univ).tendsto f
    |>.comp hf
  have hevent : (fun n => ∫ x in Set.univ, unitDensityL1 n x ∂unitHaar) =ᶠ[atTop]
      (fun _ => (1 : ℝ)) := by
    filter_upwards with n
    rw [setIntegral_univ, unitDensityL1_integral]
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hevent.symm)
  simpa only [setIntegral_univ] using h

theorem unitDensityL1_nonneg (n : ℕ) : (0 : Lp ℝ 1 unitHaar) ≤ unitDensityL1 n := by
  apply (Lp.coeFn_nonneg (unitDensityL1 n)).mp
  unfold unitDensityL1
  filter_upwards [(integrable_cylinderFunction unitHaar (n + 1)
    (density (n + 1))).coeFn_toL1] with x hx
  rw [hx]
  exact density_nonneg (n + 1) (PadicInt.toZModPow (n + 1) x)

theorem unitDensityL1_limit_nonneg (f : Lp ℝ 1 unitHaar)
    (hf : Tendsto unitDensityL1 atTop (𝓝 f)) : (0 : Lp ℝ 1 unitHaar) ≤ f := by
  have hclosed : IsClosed (Set.Ici (0 : Lp ℝ 1 unitHaar)) := isClosed_Ici
  exact hclosed.mem_of_tendsto hf (Eventually.of_forall unitDensityL1_nonneg)

theorem unitDensityL1_cylinder_integral {k : ℕ} (hk : 1 ≤ k)
    (f : Lp ℝ 1 unitHaar) (hf : Tendsto unitDensityL1 atTop (𝓝 f))
    (r : ZMod (3 ^ k)) :
    (∫ x in cylinder k r, f x ∂unitHaar) = (syracuseLaw k r).toReal := by
  have hlim := (continuous_setIntegral (μ := unitHaar) (E := ℝ)
    (cylinder k r)).tendsto f |>.comp hf
  have hevent : (fun n => ∫ x in cylinder k r, unitDensityL1 n x ∂unitHaar) =ᶠ[atTop]
      (fun _ => (syracuseLaw k r).toReal) := by
    filter_upwards [eventually_ge_atTop (k - 1)] with n hn
    have hkn : k ≤ n + 1 := by omega
    calc
      (∫ x in cylinder k r, unitDensityL1 n x ∂unitHaar) =
          ∫ x in cylinder k r, cylinderFunction (n + 1) (density (n + 1)) x ∂unitHaar :=
        integral_congr_ae (ae_restrict_of_ae
          (integrable_cylinderFunction unitHaar (n + 1) (density (n + 1))).coeFn_toL1)
      _ = _ := by
        exact unitDensityStep_cylinder_integral hk hkn (by omega) r
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hevent.symm)

end SyracuseReport
