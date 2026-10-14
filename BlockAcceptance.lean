import BlockTail
import BlockWindowBounds
import BlockRejectionSummable
import PaperStatements

/-! The fixed-block acceptance theorem for the exact finite selected families. -/

namespace SyracuseReport
open Erdos1135.Tao
open scoped BigOperators

theorem word_letters_injective : Function.Injective Word.letters := by
  intro w v h
  have hh := congrArg Word.ofReverseList h
  simpa only [Word.ofReverseList_letters] using hh

theorem blockProbability_eq_geometric_mass (j : ℕ) :
    ((geom2PNatListPMF (blockLength j)).toOuterMeasure
      ((selectedBlock j).image Word.letters : Finset (List ℕ+))).toReal =
      blockProbability j := by
  classical
  rw [PMF.toOuterMeasure_apply_finset,
    ENNReal.toReal_sum (fun a ha => PMF.apply_ne_top _ _)]
  rw [Finset.sum_image (fun w hw v hv h => word_letters_injective h)]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen : w.letters.length = blockLength j := by
    simpa only [Word.length_letters] using selectedBlock_length hw
  rw [← hlen, geom2PNatListPMF_apply_length_toReal, geom2PNatListMass_eq_inv_pow]
  simp only [taoTupleWeight, ← Word.total_ofReverseList, Word.ofReverseList_letters,
    Word.probability]

theorem block_rejection_le_list_tail (j : ℕ) :
    1 - blockProbability j ≤
      ((geom2PNatListPMF (blockLength j)).toOuterMeasure
        {as | (blockWindow j : ℝ) < |taoGeom2CenteredListWeight as|}).toReal := by
  classical
  let p := geom2PNatListPMF (blockLength j)
  let S : Finset (List ℕ+) := (selectedBlock j).image Word.letters
  let T : Set (List ℕ+) :=
    {as | (blockWindow j : ℝ) < |taoGeom2CenteredListWeight as|}
  have hcover : p.support ⊆ (S : Set (List ℕ+)) ∪ T := by
    intro as has
    have hlen := geom2PNatListPMF_support_length_eq has
    let w := Word.ofReverseList as
    have hwlen : w.length = blockLength j := by
      simpa only [w, Word.length_ofReverseList] using hlen
    by_cases hw : w ∈ selectedBlock j
    · apply Or.inl
      exact Finset.mem_image.mpr ⟨w, hw, Word.letters_ofReverseList as⟩
    · apply Or.inr
      have hfail : ¬ (2 * blockLength j ≤ w.total + blockWindow j ∧
          w.total ≤ 2 * blockLength j + blockWindow j) := by
        intro hh
        exact hw ((mem_selectedBlock_iff j w).mpr ⟨hwlen, hh⟩)
      have htotal : taoTupleWeight as = w.total := by
        simp only [w, taoTupleWeight, Word.total_ofReverseList]
      change (blockWindow j : ℝ) < |taoGeom2CenteredListWeight as|
      unfold taoGeom2CenteredListWeight
      rw [htotal, hlen]
      by_cases hlo : 2 * blockLength j ≤ w.total + blockWindow j
      · have hhi : 2 * blockLength j + blockWindow j < w.total := by omega
        have hr : 2 * (blockLength j : ℝ) + blockWindow j < w.total := by
          exact_mod_cast hhi
        exact lt_abs.mpr (Or.inl (by linarith))
      · have hhi : w.total + blockWindow j < 2 * blockLength j := by omega
        have hr : (w.total : ℝ) + blockWindow j < 2 * blockLength j := by
          exact_mod_cast hhi
        exact lt_abs.mpr (Or.inr (by linarith))
  have hone : p.toOuterMeasure ((S : Set (List ℕ+)) ∪ T) = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff _).mpr hcover
  have hunion := MeasureTheory.measure_union_le
    (μ := p.toOuterMeasure) (S : Set (List ℕ+)) T
  rw [hone] at hunion
  have hfinite (E : Set (List ℕ+)) : p.toOuterMeasure E ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure E ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite _, hfinite _⟩) hunion
  rw [ENNReal.toReal_one, ENNReal.toReal_add (hfinite _) (hfinite _)] at hr
  have hmass : (p.toOuterMeasure (S : Set (List ℕ+))).toReal = blockProbability j :=
    blockProbability_eq_geometric_mass j
  rw [hmass] at hr
  linarith

theorem block_rejection_bound (j : ℕ) :
    1 - blockProbability j ≤
      2 * Real.exp (-((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12) := by
  have hb : 0 < blockLength j := lt_of_lt_of_le (by norm_num) (blockLength_ge_200 j)
  have hbr : (0 : ℝ) < blockLength j := by exact_mod_cast hb
  have hm : (0 : ℝ) < blockWindow j := by exact_mod_cast blockWindow_pos j
  have hsmall : (blockWindow j : ℝ) ≤ (3 / 2 : ℝ) * blockLength j := by
    have := blockWindow_real_le_tenth j
    linarith
  apply (block_rejection_le_list_tail j).trans
  apply (centeredList_absTail_le_twelve hb hm hsmall).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hlo := blockWindow_real_ge_rpow j
  have hpow : (blockLength j : ℝ) ^ (6 / 5 : ℝ) ≤ (blockWindow j : ℝ) ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity :
      0 ≤ (blockLength j : ℝ) ^ (3 / 5 : ℝ)) hlo 2
    have he : ((blockLength j : ℝ) ^ (3 / 5 : ℝ)) ^ 2 =
        (blockLength j : ℝ) ^ (6 / 5 : ℝ) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hbr.le]
      norm_num
    rwa [he] at hh
  have hid : (blockLength j : ℝ) ^ (6 / 5 : ℝ) =
      (blockLength j : ℝ) ^ (1 / 5 : ℝ) * blockLength j := by
    rw [show (6 / 5 : ℝ) = 1 / 5 + 1 by norm_num,
      Real.rpow_add hbr, Real.rpow_one]
  rw [hid] at hpow
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * blockLength j)
    (by norm_num : (0 : ℝ) < 12)).mpr
  nlinarith

theorem paper_lem_block_probability : PaperStatements.lem_block_probability := by
  refine ⟨?_, prefixProbability_inf_pos_of_rejection_bound block_rejection_bound⟩
  intro j
  exact ⟨blockProbability_pos j, blockProbability_le_one j, block_rejection_bound j⟩

end SyracuseReport
