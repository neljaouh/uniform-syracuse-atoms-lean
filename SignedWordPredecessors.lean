import CountingTransfer

/-! Exact signed inverse arithmetic for admissible words. All divisibility
and orbit statements concern the concrete integer Collatz map. -/

namespace SyracuseReport

theorem inverseInteger_equation (w : Word) (R : ℤ) (hw : Contributes w R) :
    (3 : ℤ) ^ w.length * inverseInteger w R =
      (2 : ℤ) ^ w.total * R - w.numerator := by
  exact Int.mul_ediv_cancel' hw

theorem inverseInteger_nil (R : ℤ) : inverseInteger Word.nil R = R := by
  simp [inverseInteger, inverseNumerator]

theorem oneLetter_inverse_equation (a : ℕ+) (R : ℤ)
    (hw : Contributes (oneLetterWord a) R) :
    3 * inverseInteger (oneLetterWord a) R + 1 = (2 : ℤ) ^ (a : ℕ) * R := by
  have he := inverseInteger_equation (oneLetterWord a) R hw
  simp only [oneLetterWord_length, oneLetterWord_total,
    oneLetterWord_numerator, pow_one, Nat.cast_one] at he
  linarith

theorem odd_inverse_of_equation {S R : ℤ} {a : ℕ} (ha : 1 ≤ a)
    (he : 3 * S + 1 = (2 : ℤ) ^ a * R) : Odd S := by
  apply ZMod.intCast_eq_one_iff_odd.mp
  have hpow : (2 : ZMod 2) ^ a = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : a ≠ 0)]
  have hc := congrArg (fun z : ℤ => (z : ZMod 2)) he
  push_cast at hc
  rw [hpow, zero_mul, show (3 : ZMod 2) = 1 by decide, one_mul] at hc
  rw [← show (-(1 : ZMod 2)) = 1 by decide]
  exact eq_neg_of_add_eq_zero_left hc

theorem sign_inverse_of_equation {S R : ℤ} {a : ℕ} (ha : 1 ≤ a)
    (hR : R ≠ 0) (he : 3 * S + 1 = (2 : ℤ) ^ a * R) : 0 < S * R := by
  have hp : (2 : ℤ) ≤ (2 : ℤ) ^ a := by
    have hpa : (1 : ℤ) + a ≤ (2 : ℤ) ^ a := by
      simpa using (one_add_mul_le_pow (a := (1 : ℤ)) (by omega) a)
    omega
  rcases lt_or_gt_of_ne hR with hneg | hpos
  · have hR1 : R ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hR1 (by positivity : 0 ≤ (2 : ℤ) ^ a)
    have hS : S < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg hS hneg
  · have hR1 : 1 ≤ R := by omega
    have hmul := mul_le_mul_of_nonneg_left hR1 (by positivity : 0 ≤ (2 : ℤ) ^ a)
    have hS : 0 < S := by nlinarith
    exact mul_pos hS hpos

/-- Every contributing word at an odd nonzero root gives an odd source
which reaches the root and has its sign. -/
theorem contributing_word_actual_predecessor (w : Word) (R : ℤ)
    (hR : Odd R) (hw : Contributes w R) :
    Odd (inverseInteger w R) ∧ Reaches (inverseInteger w R) R ∧
      0 < inverseInteger w R * R := by
  induction w with
  | nil =>
      rw [inverseInteger_nil]
      have hRne : R ≠ 0 := by intro hz; subst R; norm_num at hR
      exact ⟨hR, ⟨0, rfl⟩, mul_self_pos.mpr hRne⟩
  | snoc w a ih =>
      have hdecomp : Word.snoc w a = w.concat (oneLetterWord a) := rfl
      rw [hdecomp, contributes_concat] at hw
      obtain ⟨hSodd, hSR, hSsign⟩ := ih hw.1
      let S := inverseInteger w R
      let M := inverseInteger (oneLetterWord a) S
      have he : 3 * M + 1 = (2 : ℤ) ^ (a : ℕ) * S :=
        oneLetter_inverse_equation a S hw.2
      have hM : Odd M := odd_inverse_of_equation a.pos he
      have hSM : Reaches M S := reaches_of_seed_equation a.pos hM he
      have hSnonzero : S ≠ 0 := by
        intro hz
        change 0 < S * R at hSsign
        rw [hz, zero_mul] at hSsign
        exact (lt_irrefl 0 hSsign)
      have hMsign : 0 < M * S := sign_inverse_of_equation a.pos hSnonzero he
      have hMRsign : 0 < M * R := by
        have hmult := mul_pos hMsign hSsign
        have heq : (M * S) * (S * R) = (M * R) * S ^ 2 := by ring
        rw [heq] at hmult
        exact (mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hSnonzero)).mp hmult
      rw [hdecomp, inverseInteger_concat w (oneLetterWord a) R hw.1]
      exact ⟨hM, hSM.trans hSR, hMRsign⟩

theorem inverseInteger_injective_fixed_statistics (R : ℤ) (d A : ℕ) :
    Set.InjOn (fun w : Word => inverseInteger w R)
      {w | w.length = d ∧ w.total = A ∧ Contributes w R} := by
  intro w hw v hv heq
  change inverseInteger w R = inverseInteger v R at heq
  apply Word.fixed_total_numerator_injective w v (hw.1.trans hv.1.symm)
    (hw.2.1.trans hv.2.1.symm)
  have hew := inverseInteger_equation w R hw.2.2
  have hev := inverseInteger_equation v R hv.2.2
  rw [hw.1, hw.2.1] at hew
  rw [hv.1, hv.2.1, ← heq] at hev
  exact_mod_cast (by linarith : (w.numerator : ℤ) = v.numerator)

theorem inverseInteger_real (w : Word) (R : ℤ) (hw : Contributes w R) :
    (inverseInteger w R : ℝ) =
      ((2 : ℝ) ^ w.total / (3 : ℝ) ^ w.length) * ((R : ℝ) - w.beta) := by
  have hi := inverseInteger_equation w R hw
  have hiR : (3 : ℝ) ^ w.length * (inverseInteger w R : ℝ) =
      (2 : ℝ) ^ w.total * (R : ℝ) - w.numerator := by exact_mod_cast hi
  unfold Word.beta
  field_simp
  nlinarith

theorem inverseInteger_abs_bound (w : Word) (R : ℤ) (hw : Contributes w R)
    {B : ℝ} (hB : w.beta ≤ B) :
    |(inverseInteger w R : ℝ)| ≤
      ((2 : ℝ) ^ w.total / (3 : ℝ) ^ w.length) * (|(R : ℝ)| + B) := by
  rw [inverseInteger_real w R hw, abs_mul,
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ w.total / (3 : ℝ) ^ w.length)]
  have hbeta : |w.beta| = w.beta := abs_of_nonneg w.beta_nonneg
  have ht := abs_sub (R : ℝ) w.beta
  rw [hbeta] at ht
  exact mul_le_mul_of_nonneg_left (ht.trans (by linarith)) (by positivity)

/-- One fixed-length, fixed-total admissible family gives that many
distinct signed odd predecessors below its common affine size bound. -/
theorem word_family_le_oddRootPredecessorCount (V : Finset Word) (R : ℤ)
    (hR : Odd R) (d A : ℕ) (x : ℝ)
    (hstats : ∀ w ∈ V, w.length = d ∧ w.total = A)
    (hadmissible : ∀ w ∈ V, Contributes w R)
    (hsize : ∀ w ∈ V, |(inverseInteger w R : ℝ)| ≤ x) :
    V.card ≤ oddRootPredecessorCount R x := by
  classical
  have hinj : Set.InjOn (fun w : Word => inverseInteger w R) V := by
    intro w hw v hv heq
    exact inverseInteger_injective_fixed_statistics R d A
      ⟨(hstats w hw).1, (hstats w hw).2, hadmissible w hw⟩
      ⟨(hstats v hv).1, (hstats v hv).2, hadmissible v hv⟩ heq
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro m hm
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hm
  have hactual := contributing_word_actual_predecessor w R hR (hadmissible w hw)
  have hbounded := abs_le.mp (hsize w hw)
  simp only [oddRootPredecessorCount, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Int.ceil_le.mpr hbounded.1, Int.le_floor.mpr hbounded.2⟩,
    hactual.1, hactual.2.1, hactual.2.2⟩

end SyracuseReport
