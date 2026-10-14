import ConcreteKernel

namespace SyracuseReport

theorem inverseNumerator_shift (w : Word) (q : ℕ) (M t : ℤ) :
    inverseNumerator w (M + t * (3 : ℤ) ^ (w.length + q)) =
      inverseNumerator w M + (3 : ℤ) ^ w.length *
        ((2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q) := by
  unfold inverseNumerator
  rw [pow_add]
  ring

theorem contributes_shift (w : Word) (q : ℕ) (M t : ℤ) :
    Contributes w (M + t * (3 : ℤ) ^ (w.length + q)) ↔ Contributes w M := by
  unfold Contributes
  rw [inverseNumerator_shift]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - ((2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q), ?_⟩
    calc
      inverseNumerator w M =
          (inverseNumerator w M + (3 : ℤ) ^ w.length *
            ((2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q)) -
            (3 : ℤ) ^ w.length * ((2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q) := by ring
      _ = _ := by rw [hk]; ring
  · rintro ⟨k, hk⟩
    refine ⟨k + ((2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q), ?_⟩
    rw [hk]
    ring

theorem inverseInteger_shift (w : Word) (q : ℕ) (M t : ℤ) :
    inverseInteger w (M + t * (3 : ℤ) ^ (w.length + q)) =
      inverseInteger w M + (2 : ℤ) ^ w.total * t * (3 : ℤ) ^ q := by
  unfold inverseInteger
  rw [inverseNumerator_shift, Int.add_mul_ediv_left _ _ (by positivity)]

/-- The concrete transport is independent of the chosen integer output
representative, at precisely the output modulus used in the report. -/
theorem wordTransport_representative_independent (w : Word) (q : ℕ) (M t : ℤ)
    (h : ZMod (3 ^ q) → ℝ) :
    wordTransport w q (M + t * (3 : ℤ) ^ (w.length + q)) h = wordTransport w q M h := by
  classical
  have hr : (inverseInteger w (M + t * (3 : ℤ) ^ (w.length + q)) : ZMod (3 ^ q)) =
      (inverseInteger w M : ZMod (3 ^ q)) := by
    rw [inverseInteger_shift]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    have hp : (3 : ZMod (3 ^ q)) ^ q = 0 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (3 ^ q)
    rw [hp]
    simp
  unfold wordTransport
  rw [contributes_shift, hr]

end SyracuseReport
