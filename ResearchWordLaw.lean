import ResearchCollisionFibre
import TransportAllWords
import WordFamilyMass

/-! The finite Syracuse atom as a sum of fixed-length geometric word
probabilities. This is the bridge from the finite fibre estimate to the
actual Syracuse law. -/

namespace SyracuseReport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem wordTransport_zero_eq_scaled_probability (w : Word) (d : ℕ)
    (hw : w.length = d) (R : ℤ) :
    wordTransport w 0 R (density 0) =
      ((2 / 3 : ℝ) * (3 : ℝ) ^ d) *
        (if Contributes w R then w.probability else 0) := by
  rw [wordTransport_depth_zero]
  by_cases h : Contributes w R
  · simp [h, Word.coefficient, Word.probability, hw, div_eq_mul_inv]
    ring
  · simp [h]

theorem finite_syracuse_atom_word_sum (d : ℕ) (R : ℤ) :
    (syracuseLaw d (R : ZMod (3 ^ d))).toReal =
      ∑' w : {w : Word // w.length = d},
        if Contributes w.1 R then w.1.probability else 0 := by
  let c : ℝ := (2 / 3 : ℝ) * (3 : ℝ) ^ d
  let f : Word → ℝ := fun w => if Contributes w R then w.probability else 0
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hpoint (w : Word) :
      (if w.length = d then wordTransport w 0 R (density 0) else 0) =
        c * (if w.length = d then f w else 0) := by
    by_cases hw : w.length = d
    · simp only [hw, if_true]
      exact wordTransport_zero_eq_scaled_probability w d hw R
    · simp [hw]
  have hsum : c * (syracuseLaw d (R : ZMod (3 ^ d))).toReal =
      c * ∑' w : Word, if w.length = d then f w else 0 := by
    calc
      c * (syracuseLaw d (R : ZMod (3 ^ d))).toReal =
          density d (R : ZMod (3 ^ d)) := by rfl
      _ = ∑' w : Word,
          if w.length = d then wordTransport w 0 R (density 0) else 0 := by
            simpa only [Nat.add_zero] using density_word_decomposition d 0 R
      _ = ∑' w : Word, c * (if w.length = d then f w else 0) := by
            apply tsum_congr
            exact hpoint
      _ = c * ∑' w : Word, if w.length = d then f w else 0 := by
            rw [tsum_mul_left]
  have hword : (syracuseLaw d (R : ZMod (3 ^ d))).toReal =
      ∑' w : Word, if w.length = d then f w else 0 :=
    (mul_left_cancel₀ hc hsum)
  rw [hword]
  exact tsum_length_eq_subtype d f

end SyracuseReport
