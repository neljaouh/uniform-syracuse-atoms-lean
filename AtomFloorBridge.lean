import SelectedCoreWitness
import Criterion

/-! The paper's actual selected-prefix construction supplies a positive
cylinder. Bounded inverses spread it to every unit residue, after which
the minimum-atom arguments give Theorem A.
-/
namespace SyracuseReport

theorem positive_syracuse_cylinder :
    ∃ (q : ℕ) (y : ZMod (3 ^ q)) (a : ℝ),
      1 ≤ q ∧ IsUnit y ∧ 0 < a ∧
      ∀ h, (hqh : q ≤ h) → ∀ x : ZMod (3 ^ h),
        residueProjection hqh x = y → a ≤ density h x := by
  obtain ⟨C, W, hC, hmark, hexcess, hs, hactual⟩ := paper_thm_construction
  exact W.positive_cylinder

theorem atom_floor : AtomFloorStatement := by
  obtain ⟨q, y, a, _, _, ha, hcyl⟩ := positive_syracuse_cylinder
  obtain ⟨d, hd, hfloor⟩ := uniform_density_of_positive_cylinder ha hcyl
  refine ⟨(3 / 2 : ℝ) * d, by positivity, ?_⟩
  intro n hn r hr
  apply atom_bound_of_density n (syracuseLaw n r).toReal d
  exact hfloor n hn r hr

theorem main_theorem_A : MainTheoremA := by
  obtain ⟨c, hc, hF⟩ := atom_floor
  obtain ⟨ell, hell, hupper, hlim⟩ := exists_normalizedMinimum_limit hc hF
  exact ⟨⟨c, hc, hF⟩, normalizedMinimum_antitone, ell, hell, hupper, hlim,
    tendsto_leastAtom_ratio hell hlim, tendsto_minimumExponent_one hc hF hell hlim⟩

end SyracuseReport
