import FiniteTransport
import Mathlib.Data.Int.GCD

/-! Exact composition of word transports, including divisibility of the
outer prefix and the nested integer inverse identity. These identities are
used in the block increments of the remaining manuscript.
-/

namespace SyracuseReport

theorem inverseNumerator_concat (w v : Word) (M : ℤ) :
    inverseNumerator (w.concat v) M =
      (2 : ℤ) ^ v.total * inverseNumerator w M -
        (3 : ℤ) ^ w.length * v.numerator := by
  simp only [inverseNumerator, Word.total_concat, Word.numerator_concat,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

theorem inverseNumerator_concat_of_contributes (w v : Word) (M : ℤ)
    (hw : Contributes w M) :
    inverseNumerator (w.concat v) M =
      (3 : ℤ) ^ w.length * inverseNumerator v (inverseInteger w M) := by
  have hi : inverseNumerator w M = (3 : ℤ) ^ w.length * inverseInteger w M :=
    (Int.mul_ediv_cancel' hw).symm
  rw [inverseNumerator_concat, hi]
  unfold inverseNumerator
  ring

/-- A contributing concatenation has a contributing outer prefix. -/
theorem contributes_prefix (w v : Word) (M : ℤ)
    (h : Contributes (w.concat v) M) : Contributes w M := by
  have hc : Nat.Coprime (3 ^ w.length) (2 ^ v.total) :=
    ((by decide : Nat.Coprime 3 2).pow_left w.length).pow_right v.total
  have hg : Int.gcd ((3 : ℤ) ^ w.length) ((2 : ℤ) ^ v.total) = 1 := by
    simpa [Int.gcd, Int.natAbs_pow] using hc
  have hd : (3 : ℤ) ^ w.length ∣ inverseNumerator (w.concat v) M := by
    apply dvd_trans (show (3 : ℤ) ^ w.length ∣ (3 : ℤ) ^ (w.concat v).length from ?_) h
    rw [Word.length_concat, pow_add]
    exact dvd_mul_right _ _
  have hm : (3 : ℤ) ^ w.length ∣ (2 : ℤ) ^ v.total * inverseNumerator w M := by
    have hsum := dvd_add hd (dvd_mul_right ((3 : ℤ) ^ w.length) (v.numerator : ℤ))
    rw [inverseNumerator_concat] at hsum
    simpa only [sub_add_cancel] using hsum
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hm hg

theorem contributes_concat (w v : Word) (M : ℤ) :
    Contributes (w.concat v) M ↔
      Contributes w M ∧ Contributes v (inverseInteger w M) := by
  constructor
  · intro h
    have hw := contributes_prefix w v M h
    refine ⟨hw, ?_⟩
    unfold Contributes at h ⊢
    rw [Word.length_concat, pow_add, inverseNumerator_concat_of_contributes w v M hw] at h
    exact (mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ w.length ≠ 0)).mp h
  · rintro ⟨hw, hv⟩
    unfold Contributes
    rw [Word.length_concat, pow_add, inverseNumerator_concat_of_contributes w v M hw]
    exact mul_dvd_mul_left _ hv

theorem inverseInteger_concat (w v : Word) (M : ℤ)
    (hw : Contributes w M) :
    inverseInteger (w.concat v) M = inverseInteger v (inverseInteger w M) := by
  unfold inverseInteger
  rw [inverseNumerator_concat_of_contributes w v M hw, Word.length_concat, pow_add]
  rw [mul_comm ((3 : ℤ) ^ w.length) (inverseNumerator v (inverseInteger w M)),
    mul_comm ((3 : ℤ) ^ w.length) ((3 : ℤ) ^ v.length)]
  exact Int.mul_ediv_mul_of_pos_left _ _ (by positivity : (0 : ℤ) < 3 ^ w.length)

/-- Exact composition of the concrete transport operators in outer-first order. -/
theorem wordTransport_concat (w v : Word) (q : ℕ) (M : ℤ)
    (h : ZMod (3 ^ q) → ℝ) :
    wordTransport (w.concat v) q M h =
      wordTransport w (v.length + q) M (finiteTransport v q h) := by
  classical
  by_cases hw : Contributes w M
  · simp only [wordTransport, contributes_concat, hw, true_and, ite_true]
    rw [finiteTransport_eq_integer]
    simp only [wordTransport, inverseInteger_concat w v M hw, Word.coefficient_concat]
    split_ifs <;> ring
  · have hnot : ¬Contributes (w.concat v) M := fun hc => hw (contributes_prefix w v M hc)
    simp only [wordTransport, if_neg hw, if_neg hnot]

end SyracuseReport
