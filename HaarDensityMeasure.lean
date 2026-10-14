import HaarDensityLimit
import Stationarity

/-! Identification of the L1 limit with the constructed Syracuse probability.
This gives absolute continuity, hence also the manuscript's pure-type result.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem exists_syracuseLimit_density :
    ∃ g : PadicInt 3 → ℝ, Integrable g additiveHaar ∧
      (∀ᵐ x ∂additiveHaar, 0 ≤ g x) ∧
      ∀ μ : Measure (PadicInt 3), IsSyracuseLimit μ →
        μ = additiveHaar.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨f, hf⟩ := exists_densityL1_limit
  let g : PadicInt 3 → ℝ := fun x => (3 / 2 : ℝ) * f x
  have hg : Integrable g additiveHaar := (L1.integrable_coeFn f).const_mul _
  have hpos : ∀ᵐ x ∂additiveHaar, 0 ≤ g x := by
    filter_upwards [(Lp.coeFn_nonneg f).mpr (densityL1_limit_nonneg f hf)] with x hx
    exact mul_nonneg (by norm_num) hx
  let ν := additiveHaar.withDensity (fun x => ENNReal.ofReal (g x))
  have hcyl (k : ℕ) (r : ZMod (3 ^ k)) : ν (cylinder k r) = syracuseLaw k r := by
    rw [withDensity_apply _ (measurableSet_cylinder k r),
      ← ofReal_integral_eq_lintegral_ofReal (hg.restrict (s := cylinder k r))
        (ae_restrict_of_ae hpos)]
    change ENNReal.ofReal (∫ x in cylinder k r, (3 / 2 : ℝ) * f x ∂additiveHaar) = _
    rw [integral_const_mul, densityL1_limit_cylinder f hf k r]
    calc
      ENNReal.ofReal ((3 / 2 : ℝ) * ((2 / 3 : ℝ) * (syracuseLaw k r).toReal)) =
          ENNReal.ofReal (syracuseLaw k r).toReal := by congr 1; ring
      _ = _ := ENNReal.ofReal_toReal ((syracuseLaw k).apply_ne_top r)
  have huniv : ν Set.univ = 1 := by
    rw [← cylinder_zero 0, hcyl]
    exact PMF.pure_apply_self (0 : ZMod (3 ^ 0))
  refine ⟨g, hg, hpos, ?_⟩
  intro μ hμ
  letI := hμ.1
  apply measure_eq_of_cylinders μ ν
  · intro k r
    exact (hμ.2 k r).trans (hcyl k r).symm
  · rw [measure_univ, huniv]

theorem syracuseLimit_absolutelyContinuous (μ : Measure (PadicInt 3))
    (hμ : IsSyracuseLimit μ) : μ ≪ additiveHaar := by
  obtain ⟨g, _hg, _hpos, hmodel⟩ := exists_syracuseLimit_density
  rw [hmodel μ hμ]
  exact withDensity_absolutelyContinuous _ _

theorem paper_lem_pure : PaperStatements.lem_pure := by
  intro μ lam hμ hLam
  rw [additiveHaar_unique lam hLam]
  exact Or.inl (syracuseLimit_absolutelyContinuous μ hμ)

end SyracuseReport
