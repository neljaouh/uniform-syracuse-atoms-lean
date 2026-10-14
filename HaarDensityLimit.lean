import HaarDensitySteps
import MixingBridge
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpOrder

/-! Completeness of L1 turns the finite mixing estimate into convergence of
the lifted densities. No limiting function is assumed as an input.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem liftedDensity_mixing :
    ∀ A : ℕ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n m : ℕ), 1 ≤ m → m ≤ n →
        (∫ x, |cylinderFunction n (density n) x -
          cylinderFunction m (density m) x| ∂additiveHaar) ≤
          (2 / 3 : ℝ) * C / (m : ℝ) ^ A := by
  intro A hA
  obtain ⟨C, hC, hmix⟩ := paper_thm_mixing A hA
  refine ⟨C, hC, ?_⟩
  intro n m hm hmn
  rw [integral_abs_density_difference hmn]
  exact hmix n m hm hmn

noncomputable def densityL1 (n : ℕ) : Lp ℝ 1 additiveHaar :=
  (integrable_cylinderFunction additiveHaar n (density n)).toL1
    (cylinderFunction n (density n))

theorem densityL1_dist (n m : ℕ) :
    dist (densityL1 n) (densityL1 m) =
      ∫ x, |cylinderFunction n (density n) x -
        cylinderFunction m (density m) x| ∂additiveHaar := by
  rw [dist_eq_norm]
  unfold densityL1
  rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

theorem densityL1_cauchy : CauchySeq densityL1 := by
  obtain ⟨C, _hC, hmix⟩ := liftedDensity_mixing 1 (by decide)
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (((2 / 3 : ℝ) * C) / ε))
  have hN1 : 1 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hN0 : (0 : ℝ) < N := lt_trans (by norm_num) hN1
  have hNnat : 1 ≤ N := by exact_mod_cast hN1.le
  have hratio : (2 / 3 : ℝ) * C / N < ε := by
    apply (div_lt_iff₀ hN0).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
    simpa only [mul_comm] using h
  refine ⟨N, ?_⟩
  intro n hn
  rw [densityL1_dist]
  have hb := hmix n N hNnat hn
  simp only [pow_one] at hb
  exact hb.trans_lt hratio

theorem exists_densityL1_limit :
    ∃ f : Lp ℝ 1 additiveHaar, Tendsto densityL1 atTop (𝓝 f) :=
  cauchySeq_tendsto_of_complete densityL1_cauchy

theorem densityL1_nonneg (n : ℕ) : (0 : Lp ℝ 1 additiveHaar) ≤ densityL1 n := by
  apply (Lp.coeFn_nonneg (densityL1 n)).mp
  unfold densityL1
  filter_upwards [(integrable_cylinderFunction additiveHaar n (density n)).coeFn_toL1]
    with x hx
  rw [hx]
  exact density_nonneg n (PadicInt.toZModPow n x)

theorem densityL1_limit_nonneg (f : Lp ℝ 1 additiveHaar)
    (hf : Tendsto densityL1 atTop (𝓝 f)) : (0 : Lp ℝ 1 additiveHaar) ≤ f := by
  have hclosed : IsClosed (Set.Ici (0 : Lp ℝ 1 additiveHaar)) := isClosed_Ici
  exact hclosed.mem_of_tendsto hf (Eventually.of_forall densityL1_nonneg)

theorem densityL1_limit_cylinder (f : Lp ℝ 1 additiveHaar)
    (hf : Tendsto densityL1 atTop (𝓝 f)) (k : ℕ) (r : ZMod (3 ^ k)) :
    (∫ x in cylinder k r, f x ∂additiveHaar) =
      (2 / 3 : ℝ) * (syracuseLaw k r).toReal := by
  have hlim := (continuous_setIntegral (μ := additiveHaar) (E := ℝ) (cylinder k r)).tendsto f
    |>.comp hf
  have hevent : (fun n => ∫ x in cylinder k r, densityL1 n x ∂additiveHaar) =ᶠ[atTop]
      (fun _ => (2 / 3 : ℝ) * (syracuseLaw k r).toReal) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    calc
      (∫ x in cylinder k r, densityL1 n x ∂additiveHaar) =
          ∫ x in cylinder k r, cylinderFunction n (density n) x ∂additiveHaar :=
        integral_congr_ae (ae_restrict_of_ae
          (integrable_cylinderFunction additiveHaar n (density n)).coeFn_toL1)
      _ = _ := setIntegral_liftedDensity hn r
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hevent.symm)

end SyracuseReport
