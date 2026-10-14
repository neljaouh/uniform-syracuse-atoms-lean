import ResearchTiltedLetter

/-! Product normalization of the tilted word law at every depth. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def tiltedWordWeight (w : Word) : ℝ :=
  (3 : ℝ) ^ w.length / (4 : ℝ) ^ w.total

theorem tiltedWordWeight_pos (w : Word) : 0 < tiltedWordWeight w := by
  unfold tiltedWordWeight
  positivity

@[simp] theorem tiltedWordWeight_nil : tiltedWordWeight Word.nil = 1 := by
  norm_num [tiltedWordWeight]

@[simp] theorem tiltedWordWeight_oneLetter (a : ℕ+) :
    tiltedWordWeight (oneLetterWord a) = tiltedLetterWeight a := by
  simp [tiltedWordWeight, tiltedLetterWeight]

theorem tiltedWordWeight_concat (w v : Word) :
    tiltedWordWeight (w.concat v) =
      tiltedWordWeight w * tiltedWordWeight v := by
  simp only [tiltedWordWeight, Word.length_concat, Word.total_concat, pow_add]
  ring

theorem tiltedWordWeight_probability_sq (w : Word) :
    tiltedWordWeight w = (3 : ℝ) ^ w.length * w.probability ^ 2 := by
  have hp : (4 : ℝ) ^ w.total = ((2 : ℝ) ^ w.total) ^ 2 := by
    calc
      _ = ((2 : ℝ) ^ 2) ^ w.total := by norm_num
      _ = ((2 : ℝ) ^ w.total) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold tiltedWordWeight Word.probability
  rw [hp]
  field_simp

theorem hasSum_fixedLength_tiltedWordWeight (d : ℕ) :
    HasSum (fun w : {w : Word // w.length = d} => tiltedWordWeight w.1) 1 := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} => tiltedWordWeight w.1)
          (tiltedWordWeight w0.1) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (tiltedLetterWeight a) := by
        simpa only [f, mul_one] using ih.mul_left (tiltedLetterWeight a)
      have hnonneg : 0 ≤ f := by
        intro p
        exact mul_nonneg (by unfold tiltedLetterWeight; positivity)
          (tiltedWordWeight_pos p.2.1).le
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact tiltedLetterWeight_summable.congr
          (fun a => (hinner a).tsum_eq.symm)
      have htotal : (∑' p, f p) = 1 := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact tiltedLetterWeight_total
      have hp := hs.hasSum
      rw [htotal] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} => tiltedWordWeight w.1) ∘
            outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter]
      rw [heq]
      exact hp

end SyracuseReport
