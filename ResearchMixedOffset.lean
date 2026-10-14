import ResearchGeometricMoments

/-! Mixed total-valuation and normalized-offset moments under the tilted
word probability law. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def tiltedOffsetFirstMomentFormula (d : ℕ) : ℝ :=
  ((d : ℝ) * ((d : ℝ) - 1) / 6) *
      (tiltedFirstMoment + geometricFirstMoment) +
    (d : ℝ) * tiltedFirstMoment / 3

theorem hasSum_fixedLength_tilted_total_offset (d : ℕ) :
    HasSum
      (fun w : {w : Word // w.length = d} =>
        tiltedWordWeight w.1 * (w.1.total : ℝ) *
          normalizedWordOffset w.1)
      (tiltedOffsetFirstMomentFormula d) := by
  induction d with
  | zero =>
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum
          (fun w : {w : Word // w.length = 0} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) *
              normalizedWordOffset w.1)
          (tiltedWordWeight w0.1 * (w0.1.total : ℝ) *
            normalizedWordOffset w0.1) :=
        hasSum_single w0 fun w hw =>
          (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [w0, tiltedOffsetFirstMomentFormula] using hs
  | succ d ih =>
      let f := fun p : ℕ+ × {w : Word // w.length = d} =>
        tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 *
          (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ)) *
          (normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1))
      have hinner (a : ℕ+) :
          HasSum (fun v : {w : Word // w.length = d} => f (a, v))
            (tiltedLetterWeight a *
              ((((a : ℕ) : ℝ) * ((d : ℝ) / 3)) +
                tiltedOffsetFirstMomentFormula d +
                (((a : ℕ) : ℝ) / 3) +
                ((d : ℝ) * geometricFirstMoment / 3))) := by
        have hAY := (hasSum_fixedLength_tilted_offset d).mul_left
          (tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have hV := ih.mul_left (tiltedLetterWeight a)
        have hAinc := (offset_increment_tilted_hasSum d).mul_left
          (tiltedLetterWeight a * ((a : ℕ) : ℝ))
        have hBinc := (offset_increment_total_hasSum d).mul_left
          (tiltedLetterWeight a)
        have h := ((hAY.add hV).add hAinc).add hBinc
        convert h using 1
        · funext v
          dsimp [f]
          ring
        · ring
      have houter : HasSum
          (fun a : ℕ+ =>
            tiltedLetterWeight a *
              ((((a : ℕ) : ℝ) * ((d : ℝ) / 3)) +
                tiltedOffsetFirstMomentFormula d +
                (((a : ℕ) : ℝ) / 3) +
                ((d : ℝ) * geometricFirstMoment / 3)))
          (tiltedOffsetFirstMomentFormula (d + 1)) := by
        have hfirst := tiltedFirstMoment_hasSum.mul_left
          (((d : ℝ) + 1) / 3)
        have hmass := (tiltedLetterWeight_summable.hasSum).mul_left
          (tiltedOffsetFirstMomentFormula d +
            (d : ℝ) * geometricFirstMoment / 3)
        rw [tiltedLetterWeight_total] at hmass
        have h := hfirst.add hmass
        convert h using 1
        · funext a
          ring
        · dsimp [tiltedOffsetFirstMomentFormula]
          push_cast
          ring
      have hnonneg : 0 ≤ f := by
        intro p
        dsimp [f]
        have hw : 0 ≤ tiltedLetterWeight p.1 * tiltedWordWeight p.2.1 :=
          mul_nonneg (tiltedLetterWeight_pos p.1).le
            (tiltedWordWeight_pos p.2.1).le
        have hA : 0 ≤ (((p.1 : ℕ) : ℝ) + (p.2.1.total : ℝ)) := by positivity
        have hY : 0 ≤ normalizedWordOffset p.2.1 +
            (2 : ℝ) ^ p.2.1.total / (3 : ℝ) ^ (d + 1) :=
          add_nonneg (normalizedWordOffset_nonneg _) (by positivity)
        exact mul_nonneg (mul_nonneg hw hA) hY
      have hs : Summable f := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr (fun a => (hinner a).tsum_eq.symm)
      have hsum : (∑' p, f p) = tiltedOffsetFirstMomentFormula (d + 1) := by
        rw [hs.tsum_prod]
        simp_rw [(hinner _).tsum_eq]
        exact houter.tsum_eq
      have hp := hs.hasSum
      rw [hsum] at hp
      apply (outerPrependEquiv d).hasSum_iff.mp
      have heq :
          ((fun w : {w : Word // w.length = d + 1} =>
            tiltedWordWeight w.1 * (w.1.total : ℝ) *
              normalizedWordOffset w.1) ∘ outerPrependEquiv d) = f := by
        funext p
        change tiltedWordWeight ((oneLetterWord p.1).concat p.2.1) *
          (((oneLetterWord p.1).concat p.2.1).total : ℝ) *
            normalizedWordOffset ((oneLetterWord p.1).concat p.2.1) = _
        rw [tiltedWordWeight_concat, tiltedWordWeight_oneLetter,
          Word.total_concat, oneLetterWord_total,
          normalizedWordOffset_outerPrepend]
        rw [p.2.2]
        push_cast
        ring
      rw [heq]
      exact hp

end SyracuseReport
