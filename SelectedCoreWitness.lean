import SelectedDensityBasics
import SelectedIncrementSummability
import BlockAcceptance
import SelectedDensityIncrement
import MixingBridge

/-! The selected-density telescope, with its explicit summable error tails. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators

theorem selectedDepth_monotone : Monotone selectedDepth := by
  apply monotone_nat_of_le_succ
  intro N
  have ht : terminalDepth N ≤ terminalDepth (N + 1) :=
    terminalDepth_monotone (Nat.le_succ N)
  change prefixDepth N + terminalDepth N ≤
    (prefixDepth N + blockLength N) + terminalDepth (N + 1)
  omega

theorem selectedDepth_tendsto : Tendsto selectedDepth atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  have hp := prefixDepth_lower N
  have hb : 1 ≤ baseBlockLength := by norm_num [baseBlockLength]
  have hmul : N ≤ N * baseBlockLength := Nat.le_mul_of_pos_right N hb
  exact hN.trans (hmul.trans (hp.trans (Nat.le_add_right _ _)))

theorem selectedDensity_telescope {C : ℝ}
    (hstep : ∀ N, ∀ z : ZMod (3 ^ selectedDepth (N + 1)),
      |selectedDensity (N + 1) z - selectedDensity N
        (residueProjection (selectedDepth_monotone (Nat.le_succ N)) z)| ≤
          selectedIncrementBound C N)
    (N m : ℕ) (z : ZMod (3 ^ selectedDepth (N + m))) :
    |selectedDensity (N + m) z - selectedDensity N
      (residueProjection (selectedDepth_monotone (Nat.le_add_right N m)) z)| ≤
        ∑ i ∈ Finset.range m, selectedIncrementBound C (N + i) := by
  induction m with
  | zero => simp [residueProjection]
  | succ m ih =>
      let z' := residueProjection (selectedDepth_monotone (Nat.le_succ (N + m))) z
      have hprev := ih z'
      have hnext := hstep (N + m) z
      have htri := abs_sub_le (selectedDensity (N + (m + 1)) z)
        (selectedDensity (N + m) z')
        (selectedDensity N (residueProjection
          (selectedDepth_monotone (Nat.le_add_right N m)) z'))
      have hcomp : residueProjection (selectedDepth_monotone (Nat.le_add_right N m)) z' =
          residueProjection (selectedDepth_monotone (Nat.le_add_right N (m + 1))) z := by
        exact residueProjection_comp _ _ z
      have htotal := htri.trans (add_le_add hnext hprev)
      rw [hcomp] at htotal
      rw [Finset.sum_range_succ]
      simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using
        htotal.trans_eq (add_comm _ _)

theorem selected_core_witness_of_increment {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ N, ∀ z : ZMod (3 ^ selectedDepth (N + 1)),
      |selectedDensity (N + 1) z - selectedDensity N
        (residueProjection (selectedDepth_monotone (Nat.le_succ N)) z)| ≤
          selectedIncrementBound C N) :
    ∃ W : CoreWitness,
      W.mark = sInf (Set.range prefixProbability) ∧ W.excess = 0 ∧
      Summable (selectedIncrementBound C) ∧
      ∀ N : ℕ, 1 ≤ N →
        W.depth N = selectedDepth N ∧ HEq (W.approximate N) (selectedDensity N) ∧
        W.variation N = ∑' j : ℕ, selectedIncrementBound C (N + j) := by
  have hblock := paper_lem_block_probability
  have hp : ∀ N, blockProbability N ≤ 1 := fun N => (hblock.1 N).2.1
  have hreject := fun N => (hblock.1 N).2.2
  have hs := summable_selectedIncrementBound hC hp hreject
  have hn := selectedIncrementBound_nonneg hC hp
  let W : CoreWitness := {
    depth := selectedDepth
    approximate := selectedDensity
    mark := sInf (Set.range prefixProbability)
    excess := 0
    variation := fun N => ∑' j : ℕ, selectedIncrementBound C (N + j)
    depth_positive := fun N _ => selectedDepth_positive N
    depth_tendsto := selectedDepth_tendsto
    mark_positive := hblock.2
    excess_nonnegative := le_rfl
    variation_nonnegative := fun N _ => tsum_nonneg (fun j => hn (N + j))
    variation_tendsto := by
      simpa only [Nat.add_comm] using tendsto_sum_nat_add (selectedIncrementBound C)
    positive_mark := fun N _ => selectedDensity_positive_mark N
    stabilization := by
      intro N j hN hNj hle z
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNj
      have ht := selectedDensity_telescope hstep N m z
      have hshift : Summable (fun i => selectedIncrementBound C (N + i)) := by
        simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hs
      exact ht.trans (hshift.sum_le_tsum (Finset.range m) (fun i _ => hn (N + i)))
    mean_excess := by
      intro N hN
      rw [selectedDensity_mean_excess_zero]
      simp }
  exact ⟨W, rfl, rfl, hs, fun N _ => ⟨rfl, HEq.rfl, rfl⟩⟩

theorem paper_thm_construction : PaperStatements.thm_construction := by
  obtain ⟨C, hC, hmix⟩ := paper_thm_mixing 6 (by norm_num)
  have hstep : ∀ N, ∀ z : ZMod (3 ^ selectedDepth (N + 1)),
      |selectedDensity (N + 1) z - selectedDensity N
        (residueProjection (selectedDepth_monotone (Nat.le_succ N)) z)| ≤
          selectedIncrementBound C N := by
    intro N z
    exact selectedDensity_step_bound C hmix N
      (selectedDepth_monotone (Nat.le_succ N)) z
  obtain ⟨W, hmark, hexcess, hs, hactual⟩ :=
    selected_core_witness_of_increment hC hstep
  exact ⟨C, W, hC, hmark, hexcess, hs, hactual⟩

end SyracuseReport
