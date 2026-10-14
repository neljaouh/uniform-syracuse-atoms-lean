import ResearchMixedOffset

/-! The mixed quadratic total/offset moment under the tilted word law. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def tiltedOffsetSecondMomentFormula : ℕ → ℝ
  | 0 => 0
  | d + 1 =>
      tiltedOffsetSecondMomentFormula d +
        2 * tiltedFirstMoment * tiltedOffsetFirstMomentFormula d +
        tiltedSecondMoment * ((d : ℝ) / 3) +
        (geometricTotalSecondMomentFormula d +
          2 * tiltedFirstMoment * (d : ℝ) * geometricFirstMoment +
          tiltedSecondMoment) / 3

noncomputable def tiltedOffsetSecondMomentCubic (d : ℕ) : ℝ :=
  let x : ℝ := d
  ((tiltedFirstMoment * (tiltedFirstMoment + geometricFirstMoment) +
      geometricFirstMoment ^ 2) / 9) * x * (x - 1) * (x - 2) +
    ((2 * tiltedFirstMoment ^ 2 + tiltedSecondMoment +
      geometricSecondMoment +
      2 * tiltedFirstMoment * geometricFirstMoment) / 6) * x * (x - 1) +
    (tiltedSecondMoment / 3) * x

noncomputable def tiltedOffsetCubicConstant : ℝ :=
  (tiltedFirstMoment * (tiltedFirstMoment + geometricFirstMoment) +
      geometricFirstMoment ^ 2) / 9 +
    (2 * tiltedFirstMoment ^ 2 + tiltedSecondMoment +
      geometricSecondMoment +
      2 * tiltedFirstMoment * geometricFirstMoment) / 6 +
    tiltedSecondMoment / 3

theorem tiltedOffsetSecondMomentFormula_eq_cubic (d : ℕ) :
    tiltedOffsetSecondMomentFormula d = tiltedOffsetSecondMomentCubic d := by
  induction d with
  | zero => simp [tiltedOffsetSecondMomentFormula, tiltedOffsetSecondMomentCubic]
  | succ d ih =>
      rw [tiltedOffsetSecondMomentFormula, ih]
      unfold tiltedOffsetSecondMomentCubic
      unfold tiltedOffsetFirstMomentFormula geometricTotalSecondMomentFormula
      push_cast
      ring

theorem tiltedOffsetSecondMomentFormula_le_cubic_bound (d : ℕ) :
    tiltedOffsetSecondMomentFormula d ≤
      tiltedOffsetCubicConstant * (d : ℝ) ^ 3 := by
  let x : ℝ := d
  let c3 : ℝ :=
    (tiltedFirstMoment * (tiltedFirstMoment + geometricFirstMoment) +
      geometricFirstMoment ^ 2) / 9
  let c2 : ℝ :=
    (2 * tiltedFirstMoment ^ 2 + tiltedSecondMoment +
      geometricSecondMoment +
      2 * tiltedFirstMoment * geometricFirstMoment) / 6
  let c1 : ℝ := tiltedSecondMoment / 3
  have hc3 : 0 ≤ c3 := by
    dsimp [c3]
    have := tiltedFirstMoment_nonneg
    have := geometricFirstMoment_nonneg
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    have := tiltedFirstMoment_nonneg
    have := geometricFirstMoment_nonneg
    have := tiltedSecondMoment_nonneg
    have := geometricSecondMoment_nonneg
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    exact div_nonneg tiltedSecondMoment_nonneg (by norm_num)
  have hform : tiltedOffsetSecondMomentCubic d =
      c3 * x * (x - 1) * (x - 2) +
        c2 * x * (x - 1) + c1 * x := rfl
  have hC : tiltedOffsetCubicConstant = c3 + c2 + c1 := rfl
  rw [tiltedOffsetSecondMomentFormula_eq_cubic, hform, hC]
  by_cases hd0 : d = 0
  · subst d
    simp [x]
  · have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hx : (1 : ℝ) ≤ x := by
      change (1 : ℝ) ≤ (d : ℝ)
      exact_mod_cast hdNat
    have hnonnegx : 0 ≤ x := by linarith
    have hx2 : x ≤ x ^ 2 := by
      have hp := mul_nonneg hnonnegx (by linarith : 0 ≤ x - 1)
      nlinarith [hp]
    have hx3 : x ^ 2 ≤ x ^ 3 := by
      have hp := mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 1)
      nlinarith [hp]
    have h3 : x * (x - 1) * (x - 2) ≤ x ^ 3 := by
      have hp := mul_nonneg hnonnegx (by linarith : 0 ≤ 3 * x - 2)
      nlinarith [hp]
    have h2 : x * (x - 1) ≤ x ^ 3 := by
      have hp : x * (x - 1) ≤ x ^ 2 := by nlinarith
      exact hp.trans hx3
    have h1 : x ≤ x ^ 3 := hx2.trans hx3
    calc
      c3 * x * (x - 1) * (x - 2) + c2 * x * (x - 1) + c1 * x ≤
          c3 * x ^ 3 + c2 * x ^ 3 + c1 * x ^ 3 := by
            have h3' := mul_le_mul_of_nonneg_left h3 hc3
            have h2' := mul_le_mul_of_nonneg_left h2 hc2
            have h1' := mul_le_mul_of_nonneg_left h1 hc1
            nlinarith [h3', h2', h1']
      _ = (c3 + c2 + c1) * x ^ 3 := by ring

theorem hasSum_fixedLength_tilted_total_sq_offset (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2 *
          normalizedWordOffset w.1)
      (tiltedOffsetSecondMomentFormula d) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2 *
              normalizedWordOffset w.1)
          (tiltedWordWeight w0.1 * (w0.1.total : ℝ) ^ 2 *
            normalizedWordOffset w0.1) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, normalizedWordOffset, tiltedOffsetSecondMomentFormula] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 *
          ((((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ)) ^ 2) *
          (normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1))
      have hinner (a : ℕ+) :
          HasSum (fun v : {w : Word // w.length = d} => f (a, v))
            (tiltedLetterWeight a *
              ((((a : ℕ) : ℝ) ^ 2 * ((d : ℝ) / 3)) +
                2 * ((a : ℕ) : ℝ) * tiltedOffsetFirstMomentFormula d +
                tiltedOffsetSecondMomentFormula d +
                (((a : ℕ) : ℝ) ^ 2 / 3) +
                2 * ((a : ℕ) : ℝ) *
                  ((d : ℝ) * geometricFirstMoment / 3) +
                geometricTotalSecondMomentFormula d / 3)) := by
        have h1 := (hasSum_fixedLength_tilted_offset d).mul_left
          (tiltedLetterWeight a * (((a : ℕ) : ℝ) ^ 2))
        have h2 := (hasSum_fixedLength_tilted_total_offset d).mul_left
          (2 * tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have h3 := ih.mul_left (tiltedLetterWeight a)
        have h4 := (offset_increment_tilted_hasSum d).mul_left
          (tiltedLetterWeight a * (((a : ℕ) : ℝ) ^ 2))
        have h5 := (offset_increment_total_hasSum d).mul_left
          (2 * tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have h6 := (offset_increment_total_sq_hasSum d).mul_left
          (tiltedLetterWeight a)
        have h := (((((h1.add h2).add h3).add h4).add h5).add h6)
        convert h using 1
        · funext v
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            tiltedLetterWeight a *
              ((((a : ℕ) : ℝ) ^ 2 * ((d : ℝ) / 3)) +
                2 * ((a : ℕ) : ℝ) * tiltedOffsetFirstMomentFormula d +
                tiltedOffsetSecondMomentFormula d +
                (((a : ℕ) : ℝ) ^ 2 / 3) +
                2 * ((a : ℕ) : ℝ) *
                  ((d : ℝ) * geometricFirstMoment / 3) +
                geometricTotalSecondMomentFormula d / 3))
          (tiltedOffsetSecondMomentFormula (d + 1)) := by
        have h2 := tiltedSecondMoment_hasSum.mul_left
          (((d : ℝ) + 1) / 3)
        have h1 := tiltedFirstMoment_hasSum.mul_left
          (2 * tiltedOffsetFirstMomentFormula d +
            2 * (d : ℝ) * geometricFirstMoment / 3)
        have h0 := (tiltedLetterWeight_summable.hasSum).mul_left
          (tiltedOffsetSecondMomentFormula d +
            geometricTotalSecondMomentFormula d / 3)
        rw [tiltedLetterWeight_total] at h0
        have h := (h2.add h1).add h0
        convert h using 1
        · funext a
          ring
        · dsimp [tiltedOffsetSecondMomentFormula]
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        have hwt : 0 ≤ tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 :=
          mul_nonneg (tiltedLetterWeight_pos p.1).le
            (tiltedWordWeight_pos p.2.1).le
        have hY : 0 ≤ normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1) :=
          add_nonneg (normalizedWordOffset_nonneg _) (by positivity)
        exact mul_nonneg (mul_nonneg hwt (sq_nonneg _)) hY
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) = tiltedOffsetSecondMomentFormula (d + 1) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2 *
              normalizedWordOffset w.1) ∘ outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) ^ 2 *
            normalizedWordOffset ((oneLetterWord p.1).concat p.2.1) = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total,
          normalizedWordOffset_outerPrepend]
        rw [p.2.2]
        push_cast
        ring
      rw [heq]
      exact hp

theorem tilted_offset_square_tsum_le (d : ℕ) :
    (∑' w : {w : Word // w.length = d},
      tiltedWordWeight w.1 * (w.1.total : ℝ) ^ 2 *
        normalizedWordOffset w.1) ≤
      tiltedOffsetCubicConstant * (d : ℝ) ^ 3 := by
  rw [(hasSum_fixedLength_tilted_total_sq_offset d).tsum_eq]
  exact tiltedOffsetSecondMomentFormula_le_cubic_bound d


end SyracuseReport
