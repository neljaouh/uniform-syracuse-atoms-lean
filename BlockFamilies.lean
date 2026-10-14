import BlockScales
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field

/-! Finite word families and prefix families used by the fixed-block proof. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def blockWindow (j : ℕ) : ℕ :=
  Nat.ceil ((blockLength j : ℝ) ^ (3 / 5 : ℝ))

def vectorLetter {M : ℕ} (a : Fin M) : ℕ+ :=
  ⟨(a : ℕ) + 1, Nat.succ_pos (a : ℕ)⟩

def wordOfVector {b M : ℕ} (a : Fin b → Fin M) : Word :=
  Word.ofReverseList (List.ofFn fun i => vectorLetter (a i))

@[simp] theorem wordOfVector_length {b M : ℕ} (a : Fin b → Fin M) :
    (wordOfVector a).length = b := by
  simp only [wordOfVector, Word.length_ofReverseList, List.length_ofFn]

noncomputable def wordCandidates (b M : ℕ) : Finset Word := by
  classical
  exact Finset.univ.image (wordOfVector : (Fin b → Fin M) → Word)

noncomputable def selectedBlock (j : ℕ) : Finset Word := by
  classical
  let b := blockLength j
  let m := blockWindow j
  exact (wordCandidates b (2 * b + m)).filter fun w =>
    2 * b ≤ w.total + m ∧ w.total ≤ 2 * b + m

def twoWord (b : ℕ) : Word :=
  Word.ofReverseList (List.replicate b (2 : ℕ+))

@[simp] theorem twoWord_length (b : ℕ) : (twoWord b).length = b := by
  simp [twoWord]

@[simp] theorem twoWord_total (b : ℕ) : (twoWord b).total = 2 * b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show twoWord (b + 1) = Word.snoc (twoWord b) (2 : ℕ+) by
        simp [twoWord, List.replicate_succ, Word.ofReverseList]]
      simp only [Word.total_snoc, ih]
      norm_num
      omega

theorem twoWord_mem_selectedBlock (j : ℕ) : twoWord (blockLength j) ∈ selectedBlock j := by
  classical
  let b := blockLength j
  let m := blockWindow j
  have hM : 1 < 2 * b + m := by
    have hb := blockLength_ge_200 j
    dsimp [b]
    omega
  let a : Fin b → Fin (2 * b + m) := fun _ => ⟨1, hM⟩
  have hword : wordOfVector a = twoWord b := by
    unfold wordOfVector twoWord
    apply congrArg Word.ofReverseList
    have ha : (fun i : Fin b => vectorLetter (a i)) =
        (fun _ : Fin b => (2 : ℕ+)) := by
      funext i
      rfl
    rw [ha, List.ofFn_const]
  apply Finset.mem_filter.mpr
  constructor
  · unfold wordCandidates
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hword⟩
  · simp

theorem selectedBlock_length {j : ℕ} {w : Word} (hw : w ∈ selectedBlock j) :
    w.length = blockLength j := by
  classical
  simp only [selectedBlock, Finset.mem_filter, wordCandidates,
    Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨a, rfl⟩ := hw.1
  exact wordOfVector_length a

theorem selectedBlock_total_bounds {j : ℕ} {w : Word} (hw : w ∈ selectedBlock j) :
    2 * blockLength j ≤ w.total + blockWindow j ∧
      w.total ≤ 2 * blockLength j + blockWindow j := by
  classical
  exact (Finset.mem_filter.mp hw).2

noncomputable def blockProbability (j : ℕ) : ℝ :=
  ∑ w ∈ selectedBlock j, w.probability

theorem blockProbability_pos (j : ℕ) : 0 < blockProbability j := by
  have hmem := twoWord_mem_selectedBlock j
  have hterm : 0 < (twoWord (blockLength j)).probability := by
    unfold Word.probability
    positivity
  unfold blockProbability
  exact lt_of_lt_of_le hterm <|
    Finset.single_le_sum (fun w _ => Word.probability_pos w |>.le) hmem

def prefixDepth : ℕ → ℕ
  | 0 => 0
  | N + 1 => prefixDepth N + blockLength N

noncomputable def prefixWindow : ℕ → ℕ
  | 0 => 0
  | N + 1 => prefixWindow N + blockWindow N

noncomputable def selectedPrefixes : ℕ → Finset Word
  | 0 => {Word.nil}
  | N + 1 => (selectedPrefixes N ×ˢ selectedBlock N).image fun w => w.1.concat w.2

@[simp] theorem selectedPrefixes_zero : selectedPrefixes 0 = {Word.nil} := rfl

@[simp] theorem selectedPrefixes_succ (N : ℕ) :
    selectedPrefixes (N + 1) =
      (selectedPrefixes N ×ˢ selectedBlock N).image fun w => w.1.concat w.2 := rfl

theorem selectedPrefixes_length {N : ℕ} {w : Word} (hw : w ∈ selectedPrefixes N) :
    w.length = prefixDepth N := by
  classical
  induction N generalizing w with
  | zero =>
      simp only [selectedPrefixes_zero, Finset.mem_singleton] at hw
      subst w
      rfl
  | succ N ih =>
      rw [selectedPrefixes_succ] at hw
      obtain ⟨wv, hwv, rfl⟩ := Finset.mem_image.mp hw
      have hp := (Finset.mem_product.mp hwv).1
      have hb := (Finset.mem_product.mp hwv).2
      simp only [Word.length_concat, ih hp, selectedBlock_length hb, prefixDepth]

theorem selectedPrefixes_total_bounds {N : ℕ} {w : Word}
    (hw : w ∈ selectedPrefixes N) :
    2 * prefixDepth N ≤ w.total + prefixWindow N ∧
      w.total ≤ 2 * prefixDepth N + prefixWindow N := by
  classical
  induction N generalizing w with
  | zero =>
      simp only [selectedPrefixes_zero, Finset.mem_singleton] at hw
      subst w
      simp [prefixDepth, prefixWindow, Word.total]
  | succ N ih =>
      rw [selectedPrefixes_succ] at hw
      obtain ⟨wv, hwv, rfl⟩ := Finset.mem_image.mp hw
      have hp := (Finset.mem_product.mp hwv).1
      have hb := (Finset.mem_product.mp hwv).2
      have hprefix := ih hp
      have hblock := selectedBlock_total_bounds hb
      simp only [Word.total_concat, prefixDepth, prefixWindow]
      omega

theorem selectedPrefixes_total_image_card (N : ℕ) :
    ((selectedPrefixes N).image Word.total).card ≤ 2 * prefixWindow N + 1 := by
  classical
  let lo := 2 * prefixDepth N - prefixWindow N
  let hi := 2 * prefixDepth N + prefixWindow N
  have hsub : (selectedPrefixes N).image Word.total ⊆ Finset.Icc lo hi := by
    intro A hA
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hA
    have hbounds := selectedPrefixes_total_bounds hw
    exact Finset.mem_Icc.mpr ⟨by omega, hbounds.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  dsimp [lo, hi] at hcard
  omega

noncomputable def prefixProbability (N : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, blockProbability j

theorem prefixProbability_pos (N : ℕ) : 0 < prefixProbability N := by
  unfold prefixProbability
  exact Finset.prod_pos fun j hj => blockProbability_pos j

theorem selectedPrefix_concat_injective (N : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1.concat p.2)
      (selectedPrefixes N ×ˢ selectedBlock N : Finset (Word × Word)) := by
  apply (Word.concat_pair_injective_at_lengths (prefixDepth N) (blockLength N)).mono
  rintro ⟨w, v⟩ hwv
  have hw := (Finset.mem_product.mp hwv).1
  have hv := (Finset.mem_product.mp hwv).2
  exact ⟨selectedPrefixes_length hw, selectedBlock_length hv⟩

theorem sum_selectedPrefixes_probability (N : ℕ) :
    (∑ w ∈ selectedPrefixes N, w.probability) = prefixProbability N := by
  classical
  induction N with
  | zero => norm_num [prefixProbability, selectedPrefixes, Word.probability]
  | succ N ih =>
      rw [selectedPrefixes_succ, Finset.sum_image (selectedPrefix_concat_injective N)]
      rw [Finset.sum_product]
      simp_rw [Word.probability_concat]
      calc
        (∑ x ∈ selectedPrefixes N, ∑ y ∈ selectedBlock N,
            x.probability * y.probability) =
            ∑ x ∈ selectedPrefixes N,
              x.probability * (∑ y ∈ selectedBlock N, y.probability) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
        _ = (∑ x ∈ selectedPrefixes N, x.probability) *
            (∑ y ∈ selectedBlock N, y.probability) := by
              rw [Finset.sum_mul]
        _ = prefixProbability (N + 1) := by
              rw [ih]
              simp [prefixProbability, blockProbability, Finset.prod_range_succ]

end SyracuseReport
