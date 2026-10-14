import WordOuter
import BlockFamilies

/-! Total probability of fixed-length geometric words and selected families. -/

namespace SyracuseReport
open scoped BigOperators ENNReal

theorem Word.letter_le_total (w : Word) (a : ℕ+) (ha : a ∈ w.letters) :
    (a : ℕ) ≤ w.total := by
  induction w with
  | nil => simp [Word.letters] at ha
  | snoc w b ih =>
      simp only [Word.letters, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [Word.total]
      · have hh := ih ha
        simp only [Word.total_snoc]
        omega

theorem word_mem_candidates_of_total (w : Word) (M : ℕ) (hM : w.total ≤ M) :
    w ∈ wordCandidates w.length M := by
  classical
  let l := w.letters
  let a : Fin l.length → Fin M := fun i =>
    ⟨((l.get i : ℕ+) : ℕ) - 1, by
      have hp := (l.get i).pos
      have ht := w.letter_le_total (l.get i) (List.get_mem l i)
      omega⟩
  have hvec : (fun i : Fin l.length => vectorLetter (a i)) = l.get := by
    funext i
    apply Subtype.ext
    change ((l.get i : ℕ) - 1) + 1 = (l.get i : ℕ)
    exact Nat.sub_add_cancel (l.get i).pos
  have hword : wordOfVector a = w := by
    unfold wordOfVector
    rw [hvec, List.ofFn_get]
    exact Word.ofReverseList_letters w
  have hmem : w ∈ wordCandidates l.length M := by
    unfold wordCandidates
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hword⟩
  simpa only [l, Word.length_letters] using hmem

theorem mem_selectedBlock_iff (j : ℕ) (w : Word) :
    w ∈ selectedBlock j ↔
      w.length = blockLength j ∧
      2 * blockLength j ≤ w.total + blockWindow j ∧
      w.total ≤ 2 * blockLength j + blockWindow j := by
  classical
  constructor
  · intro hw
    exact ⟨selectedBlock_length hw, selectedBlock_total_bounds hw⟩
  · rintro ⟨hlen, hlo, hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlo, hhi⟩
    have hm := word_mem_candidates_of_total w
      (2 * blockLength j + blockWindow j) hhi
    simpa only [hlen] using hm

theorem hasSum_letter_probability :
    HasSum (fun a : ℕ+ => (oneLetterWord a).probability) 1 := by
  have hne : (∑' a : ℕ+, letterLaw a) ≠ ∞ := by
    rw [letterLaw.tsum_coe]
    exact ENNReal.one_ne_top
  have hs := ENNReal.hasSum_toReal hne
  have htotal : (∑' a : ℕ+, (letterLaw a).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => letterLaw.apply_ne_top a),
      letterLaw.tsum_coe, ENNReal.toReal_one]
  rw [htotal] at hs
  have hf : (fun a : ℕ+ => (letterLaw a).toReal) =
      (fun a : ℕ+ => (oneLetterWord a).probability) := by
    funext a
    rw [letterLaw_real]
    simp only [Word.probability, oneLetterWord_total]
  rw [hf] at hs
  exact hs

theorem hasSum_fixedLength_probability (d : ℕ) :
    HasSum (fun w : {w : Word // w.length = d} => w.1.probability) 1 := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum (fun w : {w : Word // w.length = 0} => w.1.probability)
          w0.1.probability := hasSum_single w0 fun w hw =>
        (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, Word.probability] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        (oneLetterWord p.1).probability * p.2.1.probability
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (oneLetterWord a).probability := by
        simpa only [f, mul_one] using ih.mul_left (oneLetterWord a).probability
      have hnonneg : 0 ≤ f := by
        intro p
        exact mul_nonneg (Word.probability_pos _).le (Word.probability_pos _).le
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact hasSum_letter_probability.summable.congr
          (fun a => (hinner a).tsum_eq.symm)
      have htotal : (∑' p, f p) = 1 := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact hasSum_letter_probability.tsum_eq
      have hp := hs.hasSum
      rw [htotal] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} => w.1.probability) ∘
            outerPrependEquiv d) = f := by
        funext p
        change ((oneLetterWord p.1).concat p.2.1).probability = _
        exact Word.probability_concat _ _
      rw [heq]
      exact hp

theorem finite_word_probability_le_one (s : Finset Word) (d : ℕ)
    (hlen : ∀ w ∈ s, w.length = d) :
    (∑ w ∈ s, w.probability) ≤ 1 := by
  classical
  let S : Finset {w : Word // w.length = d} := s.attach.image
    (fun w => (⟨w.1, hlen w.1 w.2⟩ : {w : Word // w.length = d}))
  have hsum : (∑ w ∈ S, w.1.probability) = ∑ w ∈ s, w.probability := by
    unfold S
    rw [Finset.sum_image]
    · exact Finset.sum_attach _ _
    · intro w hw v hv h
      apply Subtype.ext
      exact congrArg (fun u : {w : Word // w.length = d} => u.1) h
  rw [← hsum, ← (hasSum_fixedLength_probability d).tsum_eq]
  exact (hasSum_fixedLength_probability d).summable.sum_le_tsum S
    (fun w hw => (Word.probability_pos w.1).le)

theorem blockProbability_le_one (j : ℕ) : blockProbability j ≤ 1 :=
  finite_word_probability_le_one (selectedBlock j) (blockLength j)
    (fun _ hw => selectedBlock_length hw)

end SyracuseReport
