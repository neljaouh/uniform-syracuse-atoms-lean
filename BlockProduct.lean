import WordProbability
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Positive infinite acceptance product from summable rejection mass. -/

namespace SyracuseReport
open scoped BigOperators Topology
open Filter

theorem positive_inf_products_of_summable_rejections (p : ℕ → ℝ)
    (hpos : ∀ j, 0 < p j) (hle : ∀ j, p j ≤ 1)
    (hs : Summable (fun j => 1 - p j)) :
    0 < sInf (Set.range (fun N => ∏ j ∈ Finset.range N, p j)) := by
  let P := fun N => ∏ j ∈ Finset.range N, p j
  have hsneg : Summable (fun j => p j - 1) := by
    simpa only [neg_sub] using hs.neg
  have hlog : Summable (fun j => Real.log (p j)) := by
    refine (Real.summable_log_one_add_of_summable hsneg).congr ?_
    intro j
    congr 1
    ring
  have hlim : Tendsto P atTop (𝓝 (Real.exp (∑' j, Real.log (p j)))) :=
    (Real.hasProd_of_hasSum_log hpos hlog.hasSum).tendsto_prod_nat
  have hanti : Antitone P := by
    apply antitone_nat_of_succ_le
    intro N
    dsimp [P]
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun j hj => (hpos j).le) (hle N)
  have hbelow : BddBelow (Set.range P) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact Finset.prod_nonneg fun j hj => (hpos j).le
  have hinf : Tendsto P atTop (𝓝 (sInf (Set.range P))) :=
    tendsto_atTop_ciInf hanti hbelow
  have heq := tendsto_nhds_unique hinf hlim
  rw [heq]
  exact Real.exp_pos _

theorem prefixProbability_inf_pos_of_summable
    (hs : Summable (fun j => 1 - blockProbability j)) :
    0 < sInf (Set.range prefixProbability) := by
  exact positive_inf_products_of_summable_rejections blockProbability
    blockProbability_pos blockProbability_le_one hs

end SyracuseReport
