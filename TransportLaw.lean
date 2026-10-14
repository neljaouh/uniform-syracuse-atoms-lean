import Composition
import SyracuseLaw

/-! The finite affine transport agrees with the recursive Syracuse law. -/

namespace SyracuseReport
open scoped BigOperators ENNReal

abbrev oneLetterWord (a : ℕ+) : Word := Word.snoc Word.nil a

@[simp] theorem oneLetterWord_length (a : ℕ+) : (oneLetterWord a).length = 1 := rfl

@[simp] theorem oneLetterWord_total (a : ℕ+) : (oneLetterWord a).total = a := by
  simp [oneLetterWord]

@[simp] theorem oneLetterWord_numerator (a : ℕ+) : (oneLetterWord a).numerator = 1 := by
  simp [oneLetterWord]

@[simp] theorem wordMap_oneLetter_eq (a : ℕ+) (n : ℕ) (z : ZMod (3 ^ n)) (M : ℤ) :
    wordMap (Word.snoc Word.nil a) n z =
        (M : ZMod (3 ^ ((Word.snoc Word.nil a).length + n))) ↔
      affineStep n a z = (M : ZMod (3 ^ (n + 1))) := by
  constructor
  · intro hw
    have he := (wordMap_eq_iff (Word.snoc Word.nil a) n z
      (M : ZMod (3 ^ ((Word.snoc Word.nil a).length + n)))).mp hw
    have hlen : (Word.snoc Word.nil a).length + n = n + 1 := by
      simp [Word.length]
      omega
    rw [hlen] at he
    norm_num at he
    rw [ZMod.cast_eq_val] at he
    have he' : (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) *
        (M : ZMod (3 ^ (n + 1))) = 3 * z.val + 1 := by
      simpa only [Word.length_snoc, Word.length_nil, zero_add, Word.total_snoc,
        Word.total_nil, Word.numerator_snoc, Word.numerator_nil, mul_zero,
        pow_zero, add_zero, Nat.one_add] using he
    have hs := affineStep_scaled n a z
    have hm : (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * affineStep n a z =
        (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * (M : ZMod (3 ^ (n + 1))) :=
      hs.trans he'.symm
    have hc := congrArg
      (fun v => ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * v) hm
    have hi : ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ *
        (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) = 1 := by
      rw [mul_comm]
      exact two_power_mul_inv (n + 1) (a : ℕ)
    simpa only [← mul_assoc, hi, one_mul] using hc
  · intro haff
    apply (wordMap_eq_iff (Word.snoc Word.nil a) n z
      (M : ZMod (3 ^ ((Word.snoc Word.nil a).length + n)))).mpr
    have hlen : (Word.snoc Word.nil a).length + n = n + 1 := by
      simp [Word.length]
      omega
    rw [hlen]
    have hs := affineStep_scaled n a z
    rw [haff] at hs
    norm_num at hs ⊢
    simpa only [Word.length_snoc, Word.length_nil, zero_add, Word.total_snoc,
      Word.total_nil, Word.numerator_snoc, Word.numerator_nil, mul_zero,
      pow_zero, add_zero, Nat.one_add] using hs

theorem wordTransport_oneLetter (a : ℕ+) (n : ℕ)
    (h : ZMod (3 ^ n) → ℝ) (M : ℤ) :
    wordTransport (oneLetterWord a) n M h =
      ∑ z : ZMod (3 ^ n),
        if affineStep n a z = (M : ZMod (3 ^ (n + 1)))
        then (3 / (2 : ℝ) ^ (a : ℕ)) * h z else 0 := by
  classical
  change wordTransport (Word.snoc Word.nil a) n M h = _
  rw [← finiteTransport_eq_integer]
  unfold finiteTransport
  apply Finset.sum_congr rfl
  intro z hz
  have hiff := wordMap_oneLetter_eq a n z M
  by_cases haff : affineStep n a z = (M : ZMod (3 ^ (n + 1)))
  · have hword := hiff.mpr haff
    simp only [hword, haff, ite_true, Word.coefficient, oneLetterWord_length,
      oneLetterWord_total, pow_one]
  · have hword : ¬wordMap (Word.snoc Word.nil a) n z =
        (M : ZMod (3 ^ ((Word.snoc Word.nil a).length + n))) :=
      fun hw => haff (hiff.mp hw)
    simp only [hword, haff, ite_false]

theorem pmf_map_apply_toReal {α β : Type*} [Fintype α] [DecidableEq β]
    (p : PMF α) (f : α → β) (y : β) :
    ((p.map f) y).toReal =
      ∑ x : α, if f x = y then (p x).toReal else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases hxy : f x = y
    · simp [hxy]
    · have hyx : ¬y = f x := Ne.symm hxy
      simp [hxy, hyx]
  · intro x hx
    split_ifs
    · exact (p.apply_ne_top x)
    · exact ENNReal.zero_ne_top

theorem wordTransport_oneLetter_density_eq (n : ℕ) (M : ℤ) (a : ℕ+) :
    wordTransport (oneLetterWord a) n M (density n) =
      ((2 / 3 : ℝ) * 3 ^ (n + 1)) *
        (letterLaw a *
          ((syracuseLaw n).map (affineStep n a))
            (M : ZMod (3 ^ (n + 1)))).toReal := by
  rw [wordTransport_oneLetter, ENNReal.toReal_mul, letterLaw_real,
    pmf_map_apply_toReal]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases haz : affineStep n a z = (M : ZMod (3 ^ (n + 1)))
  · simp only [haz, ite_true]
    unfold density
    rw [pow_succ]
    ring
  · simp only [haz, ite_false, mul_zero]

theorem summable_oneLetter_density_transport (n : ℕ) (M : ℤ) :
    Summable (fun a : ℕ+ =>
      wordTransport (oneLetterWord a) n M (density n)) := by
  let r : ZMod (3 ^ (n + 1)) := M
  have hne :
      (∑' a : ℕ+, letterLaw a *
        ((syracuseLaw n).map (affineStep n a)) r) ≠ ∞ := by
    have htop := (syracuseLaw (n + 1)).apply_ne_top r
    simpa only [syracuseLaw, PMF.bind_apply] using htop
  have hs := ENNReal.summable_toReal hne
  have hscaled := hs.mul_left ((2 / 3 : ℝ) * 3 ^ (n + 1))
  refine hscaled.congr ?_
  intro a
  exact (wordTransport_oneLetter_density_eq n M a).symm

theorem wordTransport_density_nonneg (w : Word) (q : ℕ) (M : ℤ) :
    0 ≤ wordTransport w q M (density q) := by
  rw [← finiteTransport_eq_integer]
  exact finiteTransport_nonneg w q (density q) (density_nonneg q)
    (M : ZMod (3 ^ (w.length + q)))

theorem density_one_step_transport (n : ℕ) (M : ℤ) :
    density (n + 1) (M : ZMod (3 ^ (n + 1))) =
      ∑' a : ℕ+, wordTransport (oneLetterWord a) n M (density n) := by
  let r : ZMod (3 ^ (n + 1)) := M
  have hfinite (a : ℕ+) :
      (((syracuseLaw n).map (affineStep n a)) r).toReal =
        ∑ z : ZMod (3 ^ n),
          if affineStep n a z = r then (syracuseLaw n z).toReal else 0 :=
    pmf_map_apply_toReal (syracuseLaw n) (affineStep n a) r
  have htop (a : ℕ+) :
      letterLaw a * ((syracuseLaw n).map (affineStep n a)) r ≠ ∞ :=
    ENNReal.mul_ne_top (letterLaw.apply_ne_top a)
      (((syracuseLaw n).map (affineStep n a)).apply_ne_top r)
  change (2 / 3 : ℝ) * (3 : ℝ) ^ (n + 1) *
      (syracuseLaw (n + 1) r).toReal = _
  simp only [syracuseLaw, PMF.bind_apply]
  rw [ENNReal.tsum_toReal_eq htop]
  simp_rw [ENNReal.toReal_mul, letterLaw_real, hfinite]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [wordTransport_oneLetter]
  rw [show (M : ZMod (3 ^ (n + 1))) = r by rfl]
  calc
    (2 / 3 : ℝ) * 3 ^ (n + 1) *
        ((1 / 2 ^ (a : ℕ)) *
          ∑ i : ZMod (3 ^ n),
            if affineStep n a i = r then (syracuseLaw n i).toReal else 0) =
      ∑ z : ZMod (3 ^ n),
        (((2 / 3 : ℝ) * 3 ^ (n + 1)) * (1 / 2 ^ (a : ℕ))) *
          (if affineStep n a z = r then (syracuseLaw n z).toReal else 0) := by
              rw [← mul_assoc]
              rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases haz : affineStep n a z = r
      · simp only [haz, ite_true]
        unfold density
        rw [pow_succ]
        ring
      · simp only [haz, ite_false, mul_zero]

theorem hasSum_oneLetter_density_transport (n : ℕ) (M : ℤ) :
    HasSum (fun a : ℕ+ => wordTransport (oneLetterWord a) n M (density n))
      (density (n + 1) (M : ZMod (3 ^ (n + 1)))) := by
  have h := (summable_oneLetter_density_transport n M).hasSum
  rw [← density_one_step_transport n M] at h
  exact h

@[simp] theorem wordTransport_nil (q : ℕ) (M : ℤ)
    (h : ZMod (3 ^ q) → ℝ) :
    wordTransport Word.nil q M h = h (M : ZMod (3 ^ q)) := by
  simp [wordTransport, Contributes, inverseNumerator, inverseInteger,
    Word.coefficient]

theorem density_word_decomposition_zero (t : ℕ) (M : ℤ) :
    density (0 + t) (M : ZMod (3 ^ (0 + t))) =
      ∑' w : Word,
        if w.length = 0 then wordTransport w t M (density t) else 0 := by
  rw [tsum_eq_single Word.nil]
  · simp only [Word.length_nil, ite_true, wordTransport_nil]
    rw [Nat.zero_add]
  · intro w hw
    have hlen : w.length ≠ 0 := by
      intro hzero
      exact hw ((Word.length_eq_zero_iff w).mp hzero)
    simp [hlen]

end SyracuseReport
