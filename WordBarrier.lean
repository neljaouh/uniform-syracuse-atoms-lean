import SignedWordPredecessors
set_option backward.isDefEq.respectTransparency false

/-! The inverse-prefix barrier controls the concrete affine offset. -/

namespace SyracuseReport

@[simp] theorem inversePrefixTotal_full (w : Word) :
    inversePrefixTotal w w.length = w.total := by
  unfold inversePrefixTotal
  rw [← Word.length_letters w, ← List.length_reverse (as := w.letters), List.take_length]
  simp only [List.map_id', bind_pure_comp]
  change (w.letters.reverse.map (fun a : ℕ+ => (a : ℕ))).sum = w.total
  rw [List.map_reverse, List.sum_reverse]
  have htotal := (Word.total_ofReverseList w.letters).symm.trans
    (congrArg Word.total (Word.ofReverseList_letters w))
  simpa only [bind_pure_comp, List.map_id'] using htotal

theorem inversePrefixTotal_snoc_le (w : Word) (a : ℕ+) (i : ℕ)
    (hi : i ≤ w.length) :
    inversePrefixTotal (Word.snoc w a) i = inversePrefixTotal w i := by
  unfold inversePrefixTotal
  simp only [Word.letters, List.reverse_cons]
  rw [List.take_append_of_le_length (by simpa only [List.length_reverse,
    Word.length_letters] using hi)]

theorem Word.beta_snoc (w : Word) (a : ℕ+) :
    (Word.snoc w a).beta = w.beta +
      (3 : ℝ) ^ w.length / (2 : ℝ) ^ (Word.snoc w a).total := by
  simp only [Word.beta, Word.numerator_snoc, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Word.total_snoc, pow_add]
  field_simp

theorem barrier_last_term (w : Word) (a : ℕ+) (D : ℝ)
    (hbarrier : -D ≤ (Word.snoc w a).total -
      ((Word.snoc w a).length : ℝ) * (Real.log 3 / Real.log 2)) :
    (3 : ℝ) ^ w.length / (2 : ℝ) ^ (Word.snoc w a).total ≤
      (2 : ℝ) ^ D / 3 := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) (by norm_num), Real.log_rpow (by norm_num)]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hbarrier hlog2.le
  simp only [Word.length_snoc, Nat.cast_add, Nat.cast_one] at hh
  have hcancel : (Real.log 3 / Real.log 2) * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ hlog2.ne'
  rw [sub_mul, mul_assoc, hcancel] at hh
  nlinarith

theorem beta_le_of_inversePrefix_barrier (w : Word) (D : ℝ)
    (hbarrier : ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
      -D ≤ (inversePrefixTotal w i : ℝ) -
        (i : ℝ) * (Real.log 3 / Real.log 2)) :
    w.beta ≤ ((2 : ℝ) ^ D / 3) * w.length := by
  induction w with
  | nil => simp [Word.beta]
  | snoc w a ih =>
      have hprefix : ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
          -D ≤ (inversePrefixTotal w i : ℝ) -
            (i : ℝ) * (Real.log 3 / Real.log 2) := by
        intro i hi hlen
        have hh := hbarrier i hi (by simp only [Word.length_snoc]; omega)
        rw [inversePrefixTotal_snoc_le w a i hlen] at hh
        exact hh
      have hlast := hbarrier (Word.snoc w a).length
        (by simp only [Word.length_snoc]; omega) le_rfl
      rw [inversePrefixTotal_full] at hlast
      have hterm := barrier_last_term w a D hlast
      rw [Word.beta_snoc]
      have hprev := ih hprefix
      simp only [Word.length_snoc, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem inverse_source_size_from_barrier (w : Word) (R : ℤ) (D : ℝ)
    (hw : Contributes w R)
    (hbarrier : ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
      -D ≤ (inversePrefixTotal w i : ℝ) -
        (i : ℝ) * (Real.log 3 / Real.log 2)) :
    |(inverseInteger w R : ℝ)| ≤
      ((2 : ℝ) ^ w.total / (3 : ℝ) ^ w.length) *
        (|(R : ℝ)| + ((2 : ℝ) ^ D / 3) * w.length) :=
  inverseInteger_abs_bound w R hw (beta_le_of_inversePrefix_barrier w D hbarrier)

end SyracuseReport
