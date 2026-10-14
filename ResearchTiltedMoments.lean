import ResearchTiltedWords

/-! First and second total-valuation moments for the tilted word law. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def tiltedFirstMoment : ℝ :=
  ∑' a : ℕ+, ((a : ℕ) : ℝ) * tiltedLetterWeight a

noncomputable def tiltedSecondMoment : ℝ :=
  ∑' a : ℕ+, ((a : ℕ) : ℝ) ^ 2 * tiltedLetterWeight a

noncomputable def tiltedTotalSecondMomentFormula (d : ℕ) : ℝ :=
  (d : ℝ) * tiltedSecondMoment +
    (d : ℝ) * ((d : ℝ) - 1) * tiltedFirstMoment ^ 2

theorem tiltedFirstMoment_hasSum :
    HasSum (fun a : ℕ+ => ((a : ℕ) : ℝ) * tiltedLetterWeight a)
      tiltedFirstMoment :=
  tiltedLetterWeight_firstMoment_summable.hasSum

theorem tiltedSecondMoment_hasSum :
    HasSum (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ 2 * tiltedLetterWeight a)
      tiltedSecondMoment :=
  tiltedLetterWeight_secondMoment_summable.hasSum

theorem hasSum_fixedLength_tilted_total (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        tiltedWordWeight w.1 * (w.1.total : ℝ))
      ((d : ℝ) * tiltedFirstMoment) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ))
          (tiltedWordWeight w0.1 * (w0.1.total : ℝ)) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 *
          (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ))
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (tiltedLetterWeight a *
              (((a : ℕ) : ℝ) + (d : ℝ) * tiltedFirstMoment)) := by
        have hmass :=
          (hasSum_fixedLength_tiltedWordWeight d).mul_left
            (tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have htotal := ih.mul_left (tiltedLetterWeight a)
        have h := hmass.add htotal
        convert h using 1
        · funext w
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            tiltedLetterWeight a *
              (((a : ℕ) : ℝ) + (d : ℝ) * tiltedFirstMoment))
          (((d + 1 : ℕ) : ℝ) * tiltedFirstMoment) := by
        have hmass := tiltedFirstMoment_hasSum
        have hconst := (tiltedLetterWeight_summable.hasSum).mul_left
          ((d : ℝ) * tiltedFirstMoment)
        rw [tiltedLetterWeight_total] at hconst
        have h := hmass.add hconst
        convert h using 1
        · funext a
          ring
        · push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        have hp := tiltedLetterWeight_pos p.1
        have hw := tiltedWordWeight_pos p.2.1
        positivity
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) =
          (((d + 1 : ℕ) : ℝ) * tiltedFirstMoment) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ)) ∘ outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total]
        push_cast
        ring
      rw [heq]
      exact hp

theorem hasSum_fixedLength_tilted_total_sq (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2)
      (tiltedTotalSecondMomentFormula d) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2)
          (tiltedWordWeight w0.1 * (w0.1.total : ℝ) ^ 2) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, tiltedTotalSecondMomentFormula] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 *
          (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ)) ^ 2
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (tiltedLetterWeight a *
              (((a : ℕ) : ℝ) ^ 2 +
                2 * ((a : ℕ) : ℝ) * ((d : ℝ) * tiltedFirstMoment) +
                tiltedTotalSecondMomentFormula d)) := by
        have hmass := (hasSum_fixedLength_tiltedWordWeight d).mul_left
          (tiltedLetterWeight a * (((a : ℕ) : ℝ) ^ 2))
        have hfirst := (hasSum_fixedLength_tilted_total d).mul_left
          (2 * tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have hsecond := ih.mul_left (tiltedLetterWeight a)
        have h := (hmass.add hfirst).add hsecond
        convert h using 1
        · funext w
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            tiltedLetterWeight a *
              (((a : ℕ) : ℝ) ^ 2 +
                2 * ((a : ℕ) : ℝ) * ((d : ℝ) * tiltedFirstMoment) +
                tiltedTotalSecondMomentFormula d))
          (tiltedTotalSecondMomentFormula (d + 1)) := by
        have hsecond := tiltedSecondMoment_hasSum
        have hfirst := tiltedFirstMoment_hasSum.mul_left
          (2 * (d : ℝ) * tiltedFirstMoment)
        have hmass := (tiltedLetterWeight_summable.hasSum).mul_left
          (tiltedTotalSecondMomentFormula d)
        rw [tiltedLetterWeight_total] at hmass
        have h := (hsecond.add hfirst).add hmass
        convert h using 1
        · funext a
          ring
        · dsimp [tiltedTotalSecondMomentFormula]
          push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        exact mul_nonneg
          (mul_nonneg (tiltedLetterWeight_pos p.1).le
            (tiltedWordWeight_pos p.2.1).le)
          (sq_nonneg _)
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) = tiltedTotalSecondMomentFormula (d + 1) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2) ∘
            outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) ^ 2 = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total]
        push_cast
        ring
      rw [heq]
      exact hp

theorem tiltedFirstMoment_nonneg : 0 ≤ tiltedFirstMoment := by
  unfold tiltedFirstMoment
  apply tsum_nonneg
  intro a
  exact mul_nonneg (by positivity) (tiltedLetterWeight_pos a).le

theorem tiltedSecondMoment_nonneg : 0 ≤ tiltedSecondMoment := by
  unfold tiltedSecondMoment
  apply tsum_nonneg
  intro a
  exact mul_nonneg (sq_nonneg _) (tiltedLetterWeight_pos a).le

theorem tiltedTotalSecondMomentFormula_le (d : ℕ) :
    tiltedTotalSecondMomentFormula d ≤
      (d : ℝ) ^ 2 * (tiltedSecondMoment + tiltedFirstMoment ^ 2) := by
  by_cases hd0 : d = 0
  · subst d
    simp [tiltedTotalSecondMomentFormula]
  · have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
    have h1 : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) * tiltedSecondMoment :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith))
        tiltedSecondMoment_nonneg
    have h2 : 0 ≤ (d : ℝ) * tiltedFirstMoment ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    unfold tiltedTotalSecondMomentFormula
    nlinarith

theorem tilted_total_square_tsum_le (d : ℕ) :
    (∑' w : {w : Word // w.length = d},
      tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2) ≤
      (d : ℝ) ^ 2 * (tiltedSecondMoment + tiltedFirstMoment ^ 2) := by
  rw [(hasSum_fixedLength_tilted_total_sq d).tsum_eq]
  exact tiltedTotalSecondMomentFormula_le d

end SyracuseReport
