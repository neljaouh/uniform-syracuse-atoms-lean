import ResearchOffsetMoments

/-! Total-valuation moments for the ordinary geometric word law.
The product argument parallels the tilted-law proof. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def geometricLetterWeight (a : ℕ+) : ℝ :=
  (oneLetterWord a).probability

noncomputable def geometricWordWeight (w : Word) : ℝ :=
  w.probability

theorem geometricLetterWeight_pos (a : ℕ+) : 0 < geometricLetterWeight a := by
  exact Word.probability_pos _

theorem geometricWordWeight_pos (w : Word) : 0 < geometricWordWeight w := by
  exact Word.probability_pos _

@[simp] theorem geometricWordWeight_oneLetter (a : ℕ+) :
    geometricWordWeight (oneLetterWord a) = geometricLetterWeight a := rfl

theorem geometricWordWeight_concat (w v : Word) :
    geometricWordWeight (w.concat v) =
      geometricWordWeight w * geometricWordWeight v := by
  exact Word.probability_concat w v

theorem geometricLetterWeight_total :
    (∑' a : ℕ+, geometricLetterWeight a) = 1 := by
  simpa only [geometricLetterWeight] using hasSum_letter_probability.tsum_eq

theorem geometricLetterWeight_summable : Summable geometricLetterWeight := by
  simpa only [geometricLetterWeight] using hasSum_letter_probability.summable

theorem geometricLetterWeight_secondMoment_summable :
    Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ 2 * geometricLetterWeight a) := by
  simpa only [geometricLetterWeight, Word.probability, oneLetterWord_total] using
    geometricLetter_secondMoment_summable

theorem geometricLetterWeight_firstMoment_summable :
    Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) * geometricLetterWeight a) := by
  apply Summable.of_nonneg_of_le
  · intro a
    exact mul_nonneg (by positivity) (geometricLetterWeight_pos a).le
  · intro a
    have ha : (1 : ℝ) ≤ (a : ℕ) := by exact_mod_cast a.pos
    have ha2 : ((a : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right ha2 (geometricLetterWeight_pos a).le
  · exact geometricLetterWeight_secondMoment_summable

theorem hasSum_fixedLength_geometricWordWeight (d : ℕ) :
    HasSum (fun w : {w : Word // w.length = d} => geometricWordWeight w.1) 1 := by
  simpa only [geometricWordWeight] using hasSum_fixedLength_probability d

noncomputable def geometricFirstMoment : ℝ :=
  ∑' a : ℕ+, ((a : ℕ) : ℝ) * geometricLetterWeight a

noncomputable def geometricSecondMoment : ℝ :=
  ∑' a : ℕ+, ((a : ℕ) : ℝ) ^ 2 * geometricLetterWeight a

noncomputable def geometricTotalSecondMomentFormula (d : ℕ) : ℝ :=
  (d : ℝ) * geometricSecondMoment +
    (d : ℝ) * ((d : ℝ) - 1) * geometricFirstMoment ^ 2

theorem geometricFirstMoment_hasSum :
    HasSum (fun a : ℕ+ => ((a : ℕ) : ℝ) * geometricLetterWeight a)
      geometricFirstMoment :=
  geometricLetterWeight_firstMoment_summable.hasSum

theorem geometricSecondMoment_hasSum :
    HasSum (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ 2 * geometricLetterWeight a)
      geometricSecondMoment :=
  geometricLetterWeight_secondMoment_summable.hasSum

theorem hasSum_fixedLength_geometric_total (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        geometricWordWeight w.1 * (w.1.total : ℝ))
      ((d : ℝ) * geometricFirstMoment) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            geometricWordWeight w.1 * (w.1.total : ℝ))
          (geometricWordWeight w0.1 * (w0.1.total : ℝ)) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        geometricLetterWeight p.1 * geometricWordWeight p.2.1 *
          (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ))
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (geometricLetterWeight a *
              (((a : ℕ) : ℝ) + (d : ℝ) * geometricFirstMoment)) := by
        have hmass :=
          (hasSum_fixedLength_geometricWordWeight d).mul_left
            (geometricLetterWeight a * ((a : ℕ) : ℝ))
        have htotal := ih.mul_left (geometricLetterWeight a)
        have h := hmass.add htotal
        convert h using 1
        · funext w
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            geometricLetterWeight a *
              (((a : ℕ) : ℝ) + (d : ℝ) * geometricFirstMoment))
          (((d + 1 : ℕ) : ℝ) * geometricFirstMoment) := by
        have hmass := geometricFirstMoment_hasSum
        have hconst := (geometricLetterWeight_summable.hasSum).mul_left
          ((d : ℝ) * geometricFirstMoment)
        rw [geometricLetterWeight_total] at hconst
        have h := hmass.add hconst
        convert h using 1
        · funext a
          ring
        · push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        have hp := geometricLetterWeight_pos p.1
        have hw := geometricWordWeight_pos p.2.1
        positivity
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) =
          (((d + 1 : ℕ) : ℝ) * geometricFirstMoment) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            geometricWordWeight w.1 * (w.1.total : ℝ)) ∘ outerPrependEquiv d) = f := by
        funext p
        change geometricWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) = _
        rw [geometricWordWeight_concat, geometricWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total]
        push_cast
        ring
      rw [heq]
      exact hp

theorem hasSum_fixedLength_geometric_total_sq (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        geometricWordWeight w.1 * (w.1.total : ℝ) ^ 2)
      (geometricTotalSecondMomentFormula d) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            geometricWordWeight w.1 * (w.1.total : ℝ) ^ 2)
          (geometricWordWeight w0.1 * (w0.1.total : ℝ) ^ 2) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, geometricTotalSecondMomentFormula] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        geometricLetterWeight p.1 * geometricWordWeight p.2.1 *
          (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ)) ^ 2
      have hinner (a : ℕ+) :
          HasSum (fun w : {w : Word // w.length = d} => f (a, w))
            (geometricLetterWeight a *
              (((a : ℕ) : ℝ) ^ 2 +
                2 * ((a : ℕ) : ℝ) * ((d : ℝ) * geometricFirstMoment) +
                geometricTotalSecondMomentFormula d)) := by
        have hmass := (hasSum_fixedLength_geometricWordWeight d).mul_left
          (geometricLetterWeight a * (((a : ℕ) : ℝ) ^ 2))
        have hfirst := (hasSum_fixedLength_geometric_total d).mul_left
          (2 * geometricLetterWeight a * ((a : ℕ) : ℝ))
        have hsecond := ih.mul_left (geometricLetterWeight a)
        have h := (hmass.add hfirst).add hsecond
        convert h using 1
        · funext w
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            geometricLetterWeight a *
              (((a : ℕ) : ℝ) ^ 2 +
                2 * ((a : ℕ) : ℝ) * ((d : ℝ) * geometricFirstMoment) +
                geometricTotalSecondMomentFormula d))
          (geometricTotalSecondMomentFormula (d + 1)) := by
        have hsecond := geometricSecondMoment_hasSum
        have hfirst := geometricFirstMoment_hasSum.mul_left
          (2 * (d : ℝ) * geometricFirstMoment)
        have hmass := (geometricLetterWeight_summable.hasSum).mul_left
          (geometricTotalSecondMomentFormula d)
        rw [geometricLetterWeight_total] at hmass
        have h := (hsecond.add hfirst).add hmass
        convert h using 1
        · funext a
          ring
        · dsimp [geometricTotalSecondMomentFormula]
          push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        exact mul_nonneg
          (mul_nonneg (geometricLetterWeight_pos p.1).le
            (geometricWordWeight_pos p.2.1).le)
          (sq_nonneg _)
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) = geometricTotalSecondMomentFormula (d + 1) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            geometricWordWeight w.1 * (w.1.total : ℝ) ^ 2) ∘
            outerPrependEquiv d) = f := by
        funext p
        change geometricWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) ^ 2 = _
        rw [geometricWordWeight_concat, geometricWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total]
        push_cast
        ring
      rw [heq]
      exact hp

theorem geometricFirstMoment_nonneg : 0 ≤ geometricFirstMoment := by
  unfold geometricFirstMoment
  apply tsum_nonneg
  intro a
  exact mul_nonneg (by positivity) (geometricLetterWeight_pos a).le

theorem geometricSecondMoment_nonneg : 0 ≤ geometricSecondMoment := by
  unfold geometricSecondMoment
  apply tsum_nonneg
  intro a
  exact mul_nonneg (sq_nonneg _) (geometricLetterWeight_pos a).le

theorem geometricTotalSecondMomentFormula_le (d : ℕ) :
    geometricTotalSecondMomentFormula d ≤
      (d : ℝ) ^ 2 * (geometricSecondMoment + geometricFirstMoment ^ 2) := by
  by_cases hd0 : d = 0
  · subst d
    simp [geometricTotalSecondMomentFormula]
  · have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
    have h1 : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) * geometricSecondMoment :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith))
        geometricSecondMoment_nonneg
    have h2 : 0 ≤ (d : ℝ) * geometricFirstMoment ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    unfold geometricTotalSecondMomentFormula
    nlinarith

theorem geometric_total_square_tsum_le (d : ℕ) :
    (∑' w : {w : Word // w.length = d},
      geometricWordWeight w.1 * (w.1.total : ℝ) ^ 2) ≤
      (d : ℝ) ^ 2 * (geometricSecondMoment + geometricFirstMoment ^ 2) := by
  rw [(hasSum_fixedLength_geometric_total_sq d).tsum_eq]
  exact geometricTotalSecondMomentFormula_le d

theorem offset_increment_total_hasSum (d : ℕ) :
    HasSum
      (fun v : {w : Word // w.length = d} =>
        tiltedWordWeight v.1 * (v.1.total : ℝ) *
          ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ (d + 1)))
      ((d : ℝ) * geometricFirstMoment / 3) := by
  have h := (hasSum_fixedLength_geometric_total d).mul_left (1 / 3 : ℝ)
  convert h using 1
  · funext v
    have ht := tiltedWordWeight_twist v.1
    rw [v.2] at ht
    dsimp [geometricWordWeight]
    rw [pow_succ]
    field_simp at ht ⊢
    nlinarith [ht]
  · ring

theorem offset_increment_total_sq_hasSum (d : ℕ) :
    HasSum
      (fun v : {w : Word // w.length = d} =>
        tiltedWordWeight v.1 * (v.1.total : ℝ) ^ 2 *
          ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ (d + 1)))
      (geometricTotalSecondMomentFormula d / 3) := by
  have h := (hasSum_fixedLength_geometric_total_sq d).mul_left (1 / 3 : ℝ)
  convert h using 1
  · funext v
    have ht : tiltedWordWeight v.1 *
        ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ d) = v.1.probability := by
      simpa only [v.2] using tiltedWordWeight_twist v.1
    calc
      tiltedWordWeight v.1 * (v.1.total : ℝ) ^ 2 *
          ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ (d + 1)) =
        (tiltedWordWeight v.1 *
          ((2 : ℝ) ^ v.1.total / (3 : ℝ) ^ d)) *
            (v.1.total : ℝ) ^ 2 / 3 := by
              rw [pow_succ]
              field_simp
              ring
      _ = (1 / 3 : ℝ) *
          (geometricWordWeight v.1 * (v.1.total : ℝ) ^ 2) := by
            rw [ht]
            dsimp [geometricWordWeight]
            ring
  · ring

end SyracuseReport
