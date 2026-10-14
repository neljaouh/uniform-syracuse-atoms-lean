import ResearchWordLaw
import WordProbability

/-! Finite fixed-total fibres of the actual Syracuse word expansion. -/

namespace SyracuseReport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def fixedTotalContributors (d A : ℕ) (R : ℤ) : Finset Word :=
  (wordCandidates d A).filter fun w => w.total = A ∧ Contributes w R

theorem mem_fixedTotalContributors_iff (d A : ℕ) (R : ℤ) (w : Word) :
    w ∈ fixedTotalContributors d A R ↔
      w.length = d ∧ w.total = A ∧ Contributes w R := by
  classical
  constructor
  · intro hw
    obtain ⟨hcand, htotal, hcontrib⟩ := Finset.mem_filter.mp hw
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hcand
    have hlen : w.length = d := by
      rw [← ha]
      exact wordOfVector_length a
    exact ⟨hlen, htotal, hcontrib⟩
  · rintro ⟨hlen, htotal, hcontrib⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, htotal, hcontrib⟩
    have hm := word_mem_candidates_of_total w A (by omega : w.total ≤ A)
    simpa only [hlen] using hm

theorem fixedTotalContributors_residue (d A : ℕ) (R : ℤ)
    (w : Word) (hw : w ∈ fixedTotalContributors d A R) :
    w.numerator % 3 ^ d =
      (((2 : ZMod (3 ^ d)) ^ A) * (R : ZMod (3 ^ d))).val := by
  obtain ⟨hlen, htotal, hcontrib⟩ :=
    (mem_fixedTotalContributors_iff d A R w).mp hw
  have hdvd : (3 : ℤ) ^ d ∣ (2 : ℤ) ^ A * R - w.numerator := by
    simpa only [Contributes, inverseNumerator, hlen, htotal] using hcontrib
  have hzero : (((2 : ℤ) ^ A * R - w.numerator : ℤ) : ZMod (3 ^ d)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have hcast : (2 : ZMod (3 ^ d)) ^ A * (R : ZMod (3 ^ d)) -
      (w.numerator : ZMod (3 ^ d)) = 0 := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_ofNat] using hzero
  have hnum : (w.numerator : ZMod (3 ^ d)) =
      (2 : ZMod (3 ^ d)) ^ A * (R : ZMod (3 ^ d)) :=
    (sub_eq_zero.mp hcast).symm
  exact (by simpa only [ZMod.val_natCast] using congrArg ZMod.val hnum)

theorem actual_fixed_total_fibre_quadratic_real (d A : ℕ) (R : ℤ) :
    ((fixedTotalContributors d A R).card : ℝ) ^ 2 ≤
      2 * ∑ w ∈ fixedTotalContributors d A R,
        (1 + (w.numerator : ℝ) / (3 : ℝ) ^ d) := by
  let s := fixedTotalContributors d A R
  have hstats (w : Word) (hw : w ∈ s) :
      w.length = d ∧ w.total = A ∧ Contributes w R :=
    (mem_fixedTotalContributors_iff d A R w).mp hw
  have hres (w : Word) (hw : w ∈ s) :
      w.numerator % 3 ^ d =
        (((2 : ZMod (3 ^ d)) ^ A) * (R : ZMod (3 ^ d))).val :=
    fixedTotalContributors_residue d A R w hw
  have h := fixed_total_residue_fibre_quadratic_real s d A (3 ^ d)
    ((((2 : ZMod (3 ^ d)) ^ A) * (R : ZMod (3 ^ d))).val)
    (by positivity) (fun w hw => (hstats w hw).1)
    (fun w hw => (hstats w hw).2.1) hres
  simpa only [s, Nat.cast_pow, Nat.cast_ofNat] using h

end SyracuseReport
