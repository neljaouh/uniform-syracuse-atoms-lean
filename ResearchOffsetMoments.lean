import ResearchTiltedMoments

/-! Affine-offset identities used to control the mixed tilted moment. -/

namespace SyracuseReport

noncomputable def normalizedWordOffset (w : Word) : ℝ :=
  (w.numerator : ℝ) / (3 : ℝ) ^ w.length

theorem normalizedWordOffset_nonneg (w : Word) :
    0 ≤ normalizedWordOffset w := by
  unfold normalizedWordOffset
  positivity

theorem normalizedWordOffset_outerPrepend (a : ℕ+) (v : Word) :
    normalizedWordOffset ((oneLetterWord a).concat v) =
      normalizedWordOffset v +
        (2 : ℝ) ^ v.total / (3 : ℝ) ^ (v.length + 1) := by
  unfold normalizedWordOffset
  simp only [Word.numerator_concat, Word.length_concat,
    oneLetterWord_numerator, oneLetterWord_length, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one,
    pow_one, Nat.one_add]
  rw [pow_succ]
  field_simp
  ring

theorem tiltedWordWeight_twist (w : Word) :
    tiltedWordWeight w *
      ((2 : ℝ) ^ w.total / (3 : ℝ) ^ w.length) =
        w.probability := by
  rw [tiltedWordWeight_probability_sq]
  unfold Word.probability
  field_simp

/-- The new normalized-offset term created by one outer letter has
tilted expectation exactly `1/3`, at every inner depth. -/
theorem offset_increment_tilted_hasSum (d : ℕ) :
    HasSum
      (fun v : {w : Word // w.length = d} =>
        tiltedWordWeight v.1 *
          ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ (d + 1)))
      (1 / 3 : ℝ) := by
  have h : HasSum
      (fun v : {w : Word // w.length = d} =>
        (1 / 3 : ℝ) * v.1.probability) (1 / 3 : ℝ) := by
    simpa using (hasSum_fixedLength_probability d).mul_left (1 / 3 : ℝ)
  apply h.congr_fun
  intro v
  have ht := tiltedWordWeight_twist v.1
  rw [v.2] at ht
  calc
    tiltedWordWeight v.1 *
        ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ (d + 1)) =
      (tiltedWordWeight v.1 *
        ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ d)) / 3 := by
        rw [pow_succ]
        field_simp
    _ = v.1.probability / 3 := by rw [ht]
    _ = (1 / 3 : ℝ) * v.1.probability := by ring

theorem hasSum_fixedLength_tilted_offset (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        tiltedWordWeight w.1 * normalizedWordOffset w.1)
      ((d : ℝ) / 3) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            tiltedWordWeight w.1 * normalizedWordOffset w.1)
          (tiltedWordWeight w0.1 * normalizedWordOffset w0.1) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, normalizedWordOffset] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 *
          (normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1))
      have hinner (a : ℕ+) :
          HasSum (fun v : {w : Word // w.length = d} => f (a, v))
            (tiltedLetterWeight a * (((d : ℝ) / 3) + 1 / 3)) := by
        have hprev := ih.mul_left (tiltedLetterWeight a)
        have hnew := (offset_increment_tilted_hasSum d).mul_left
          (tiltedLetterWeight a)
        have h := hprev.add hnew
        convert h using 1
        · funext v
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ => tiltedLetterWeight a * (((d : ℝ) / 3) + 1 / 3))
          (((d + 1 : ℕ) : ℝ) / 3) := by
        have h := (tiltedLetterWeight_summable.hasSum).mul_left
          (((d : ℝ) / 3) + 1 / 3)
        rw [tiltedLetterWeight_total] at h
        convert h using 1
        · funext a
          ring
        · push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        have hweight : 0 ≤ tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 :=
          mul_nonneg (tiltedLetterWeight_pos p.1).le
            (tiltedWordWeight_pos p.2.1).le
        have hoffset : 0 ≤ normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1) := by
          exact add_nonneg (normalizedWordOffset_nonneg _) (by positivity)
        exact mul_nonneg hweight hoffset
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) = (((d + 1 : ℕ) : ℝ) / 3) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            tiltedWordWeight w.1 * normalizedWordOffset w.1) ∘
            outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) *
          normalizedWordOffset ((oneLetterWord p.1).concat p.2.1) = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter,
          normalizedWordOffset_outerPrepend]
        rw [p.2.2]
      rw [heq]
      exact hp

end SyracuseReport
