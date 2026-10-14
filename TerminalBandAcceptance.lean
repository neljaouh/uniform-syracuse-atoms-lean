import BlockTail
import WordProbability

/-! Finite terminal word families with an arbitrary integer valuation band. -/

namespace SyracuseReport
open Erdos1135.Tao
open scoped BigOperators

noncomputable def terminalBandWords (t m : ℕ) : Finset Word := by
  classical
  exact (wordCandidates t (2 * t + m)).filter fun w =>
    2 * t ≤ w.total + m ∧ w.total ≤ 2 * t + m

noncomputable def terminalBandProbability (t m : ℕ) : ℝ :=
  ∑ w ∈ terminalBandWords t m, w.probability

theorem terminalBandWords_length {t m : ℕ} {w : Word}
    (hw : w ∈ terminalBandWords t m) : w.length = t := by
  classical
  simp only [terminalBandWords, Finset.mem_filter, wordCandidates,
    Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨a, rfl⟩ := hw.1
  exact wordOfVector_length a

theorem mem_terminalBandWords_iff (t m : ℕ) (w : Word) :
    w ∈ terminalBandWords t m ↔
      w.length = t ∧ 2 * t ≤ w.total + m ∧ w.total ≤ 2 * t + m := by
  classical
  constructor
  · intro hw
    exact ⟨terminalBandWords_length hw, (Finset.mem_filter.mp hw).2⟩
  · rintro ⟨hlen, hlo, hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlo, hhi⟩
    have hm := word_mem_candidates_of_total w (2 * t + m) hhi
    simpa only [hlen] using hm

theorem terminalBandProbability_pos (t m : ℕ) : 0 < terminalBandProbability t m := by
  have hmem : twoWord t ∈ terminalBandWords t m := by
    rw [mem_terminalBandWords_iff]
    simp
  unfold terminalBandProbability
  exact lt_of_lt_of_le (Word.probability_pos (twoWord t))
    (Finset.single_le_sum (fun w _ => (Word.probability_pos w).le) hmem)

theorem terminalBandProbability_le_one (t m : ℕ) : terminalBandProbability t m ≤ 1 :=
  finite_word_probability_le_one (terminalBandWords t m) t
    (fun _ hw => terminalBandWords_length hw)

theorem terminalBandProbability_eq_geometric_mass (t m : ℕ) :
    ((geom2PNatListPMF t).toOuterMeasure
      ((terminalBandWords t m).image Word.letters : Finset (List ℕ+))).toReal =
      terminalBandProbability t m := by
  classical
  have hinj : Function.Injective Word.letters := by
    intro w v h
    simpa only [Word.ofReverseList_letters] using congrArg Word.ofReverseList h
  rw [PMF.toOuterMeasure_apply_finset,
    ENNReal.toReal_sum (fun a ha => PMF.apply_ne_top _ _)]
  rw [Finset.sum_image (fun w hw v hv h => hinj h)]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen : w.letters.length = t := by
    simpa only [Word.length_letters] using terminalBandWords_length hw
  rw [← hlen, geom2PNatListPMF_apply_length_toReal, geom2PNatListMass_eq_inv_pow]
  simp only [taoTupleWeight, ← Word.total_ofReverseList, Word.ofReverseList_letters,
    Word.probability]

theorem terminalBand_rejection_le_list_tail (t m : ℕ) :
    1 - terminalBandProbability t m ≤
      ((geom2PNatListPMF t).toOuterMeasure
        {as | (m : ℝ) < |taoGeom2CenteredListWeight as|}).toReal := by
  classical
  let p := geom2PNatListPMF t
  let S : Finset (List ℕ+) := (terminalBandWords t m).image Word.letters
  let T : Set (List ℕ+) := {as | (m : ℝ) < |taoGeom2CenteredListWeight as|}
  have hcover : p.support ⊆ (S : Set (List ℕ+)) ∪ T := by
    intro as has
    have hlen := geom2PNatListPMF_support_length_eq has
    let w := Word.ofReverseList as
    have hwlen : w.length = t := by
      simpa only [w, Word.length_ofReverseList] using hlen
    by_cases hw : w ∈ terminalBandWords t m
    · apply Or.inl
      exact Finset.mem_image.mpr ⟨w, hw, Word.letters_ofReverseList as⟩
    · apply Or.inr
      have hfail : ¬ (2 * t ≤ w.total + m ∧ w.total ≤ 2 * t + m) := by
        intro hh
        exact hw ((mem_terminalBandWords_iff t m w).mpr ⟨hwlen, hh⟩)
      have htotal : taoTupleWeight as = w.total := by
        simp only [w, taoTupleWeight, Word.total_ofReverseList]
      change (m : ℝ) < |taoGeom2CenteredListWeight as|
      unfold taoGeom2CenteredListWeight
      rw [htotal, hlen]
      by_cases hlo : 2 * t ≤ w.total + m
      · have hhi : 2 * t + m < w.total := by omega
        have hr : 2 * (t : ℝ) + m < w.total := by exact_mod_cast hhi
        exact lt_abs.mpr (Or.inl (by linarith))
      · have hhi : w.total + m < 2 * t := by omega
        have hr : (w.total : ℝ) + m < 2 * t := by exact_mod_cast hhi
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
  have hmass : (p.toOuterMeasure (S : Set (List ℕ+))).toReal = terminalBandProbability t m :=
    terminalBandProbability_eq_geometric_mass t m
  rw [hmass] at hr
  linarith

theorem terminalBand_rejection_bound {t m : ℕ} (ht : 0 < t) (hm : 0 < m)
    (hsmall : (m : ℝ) ≤ (3 / 2 : ℝ) * t) :
    1 - terminalBandProbability t m ≤ 2 * Real.exp (-((m : ℝ) ^ 2) / (12 * (t : ℝ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact (terminalBand_rejection_le_list_tail t m).trans
    (centeredList_absTail_le_twelve ht hmR hsmall)

end SyracuseReport
