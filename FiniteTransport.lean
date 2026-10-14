import Transport
import Mathlib.Algebra.GroupWithZero.Divisibility

namespace SyracuseReport

open scoped BigOperators

theorem scaled_int_cast_eq_iff (d q : ℕ) (R S : ℤ) :
    (3 : ZMod (3 ^ (d + q))) ^ d * (R : ZMod (3 ^ (d + q))) =
      (3 : ZMod (3 ^ (d + q))) ^ d * (S : ZMod (3 ^ (d + q))) ↔
    (R : ZMod (3 ^ q)) = (S : ZMod (3 ^ q)) := by
  have hcast : (((3 : ℤ) ^ d * (R - S) : ℤ) : ZMod (3 ^ (d + q))) =
      (3 : ZMod (3 ^ (d + q))) ^ d *
        ((R : ZMod (3 ^ (d + q))) - (S : ZMod (3 ^ (d + q)))) := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_ofNat]
  rw [← sub_eq_zero, ← mul_sub, ← hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ d ≠ 0)]
  have hz := ZMod.intCast_zmod_eq_zero_iff_dvd (R - S) (3 ^ q)
  simpa only [Int.cast_sub, sub_eq_zero, Nat.cast_pow, Nat.cast_ofNat] using hz.symm

theorem two_power_mul_inv (n A : ℕ) :
    (2 : ZMod (3 ^ n)) ^ A * ((2 : ZMod (3 ^ n)) ^ A)⁻¹ = 1 := by
  have hc : Nat.Coprime (2 ^ A) (3 ^ n) :=
    ((by decide : Nat.Coprime 2 3).pow_left A).pow_right n
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.coe_mul_inv_eq_one (2 ^ A) hc

/-- The finite affine word map from G_q to G_(|w|+q). -/
noncomputable def wordMap (w : Word) (q : ℕ) (z : ZMod (3 ^ q)) :
    ZMod (3 ^ (w.length + q)) :=
  ((2 : ZMod (3 ^ (w.length + q))) ^ w.total)⁻¹ *
    ((3 : ZMod (3 ^ (w.length + q))) ^ w.length * z.val + w.numerator)

theorem wordMap_eq_iff (w : Word) (q : ℕ) (z : ZMod (3 ^ q))
    (r : ZMod (3 ^ (w.length + q))) :
    wordMap w q z = r ↔
      (2 : ZMod (3 ^ (w.length + q))) ^ w.total * r =
        (3 : ZMod (3 ^ (w.length + q))) ^ w.length * z.val + w.numerator := by
  have hi := two_power_mul_inv (w.length + q) w.total
  constructor
  · intro h
    rw [← h, wordMap, ← mul_assoc, hi, one_mul]
  · intro h
    unfold wordMap
    rw [← h, ← mul_assoc, mul_comm _ ((2 : ZMod (3 ^ (w.length + q))) ^ w.total),
      hi, one_mul]

theorem wordMap_injective (w : Word) (q : ℕ) : Function.Injective (wordMap w q) := by
  intro z z' h
  have h1 := (wordMap_eq_iff w q z (wordMap w q z')).mp h
  have h2 := (wordMap_eq_iff w q z' (wordMap w q z')).mp rfl
  have he : (3 : ZMod (3 ^ (w.length + q))) ^ w.length * z.val =
      (3 : ZMod (3 ^ (w.length + q))) ^ w.length * z'.val := by
    exact add_right_cancel (h1.symm.trans h2)
  have he' : (3 : ZMod (3 ^ (w.length + q))) ^ w.length * (z.val : ℤ) =
      (3 : ZMod (3 ^ (w.length + q))) ^ w.length * (z'.val : ℤ) := by
    simpa only [Int.cast_natCast] using he
  have hz := (scaled_int_cast_eq_iff w.length q z.val z'.val).mp he'
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz

theorem wordMap_of_inverseEquation (w : Word) (q : ℕ) (M R : ℤ)
    (h : InverseEquation w M R) :
    wordMap w q (R : ZMod (3 ^ q)) = (M : ZMod (3 ^ (w.length + q))) := by
  apply (wordMap_eq_iff w q (R : ZMod (3 ^ q)) _).mpr
  have hsource : (((R : ZMod (3 ^ q)).val : ℤ) : ZMod (3 ^ q)) =
      (R : ZMod (3 ^ q)) := by simp
  have hs := (scaled_int_cast_eq_iff w.length q (R : ZMod (3 ^ q)).val R).mpr hsource
  have he : (2 : ZMod (3 ^ (w.length + q))) ^ w.total * M - w.numerator =
      (3 : ZMod (3 ^ (w.length + q))) ^ w.length * R := by
    have hh := congrArg (fun n : ℤ => (n : ZMod (3 ^ (w.length + q)))) h
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat] using hh
  simp only [Int.cast_natCast] at hs
  rw [hs]
  exact (sub_eq_iff_eq_add).mp he |>.trans (by ring)

theorem wordMap_inverse_fiber (w : Word) (q : ℕ) (z : ZMod (3 ^ q)) (M : ℤ) :
    wordMap w q z = (M : ZMod (3 ^ (w.length + q))) ↔
      Contributes w M ∧ (inverseInteger w M : ZMod (3 ^ q)) = z := by
  constructor
  · intro h
    have he := (wordMap_eq_iff w q z _).mp h
    have hz : (((2 : ℤ) ^ w.total * M - w.numerator -
        (3 : ℤ) ^ w.length * z.val : ℤ) : ZMod (3 ^ (w.length + q))) = 0 := by
      push_cast
      rw [he]
      ring
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ (w.length + q))).mp hz
    obtain ⟨k, hk⟩ := hd
    have hnum : inverseNumerator w M =
        (3 : ℤ) ^ w.length * ((z.val : ℤ) + (3 : ℤ) ^ q * k) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add] at hk
      unfold inverseNumerator
      nlinarith [hk]
    have hc : Contributes w M := ⟨(z.val : ℤ) + (3 : ℤ) ^ q * k, hnum⟩
    refine ⟨hc, ?_⟩
    have hi : inverseInteger w M = (z.val : ℤ) + (3 : ℤ) ^ q * k := by
      unfold inverseInteger
      rw [hnum, Int.mul_ediv_cancel_left _ (by positivity)]
    rw [hi]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      ZMod.natCast_val]
    have hp : (3 : ZMod (3 ^ q)) ^ q = 0 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (3 ^ q)
    rw [hp]
    simp
  · rintro ⟨hc, hz⟩
    rw [← hz]
    exact wordMap_of_inverseEquation w q M (inverseInteger w M)
      (contributes_inverse_equation w M hc)

/-- Transport defined directly by summing the finite affine inverse fiber. -/
noncomputable def finiteTransport (w : Word) (q : ℕ)
    (h : ZMod (3 ^ q) → ℝ) (r : ZMod (3 ^ (w.length + q))) : ℝ := by
  classical
  exact ∑ z, if wordMap w q z = r then w.coefficient * h z else 0

theorem finiteTransport_eq_integer (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ)
    (M : ℤ) :
    finiteTransport w q h (M : ZMod (3 ^ (w.length + q))) = wordTransport w q M h := by
  classical
  unfold finiteTransport wordTransport
  simp only [wordMap_inverse_fiber]
  by_cases hc : Contributes w M
  · simp [hc, eq_comm]
  · simp [hc]

theorem finiteTransport_sum (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ) :
    (∑ r, finiteTransport w q h r) = w.coefficient * ∑ z, h z := by
  classical
  unfold finiteTransport
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum]

/-- Exact normalized mean, including the change in residue-group size. -/
theorem finiteMean_finiteTransport (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ) :
    finiteMean (finiteTransport w q h) = w.probability * finiteMean h := by
  have h2 : (2 : ℝ) ^ w.total ≠ 0 := by positivity
  have hd : (3 : ℝ) ^ w.length ≠ 0 := by positivity
  have hq : (3 : ℝ) ^ q ≠ 0 := by positivity
  unfold finiteMean
  rw [finiteTransport_sum]
  simp only [ZMod.card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Word.coefficient, Word.probability,
    pow_add]
  field_simp

theorem finiteTransport_nonneg (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ)
    (hh : ∀ z, 0 ≤ h z) (r : ZMod (3 ^ (w.length + q))) :
    0 ≤ finiteTransport w q h r := by
  classical
  unfold finiteTransport
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact mul_nonneg w.coefficient_pos.le (hh z)
  · exact le_rfl

theorem finiteTransport_abs (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ)
    (r : ZMod (3 ^ (w.length + q))) :
    |finiteTransport w q h r| = finiteTransport w q (fun z => |h z|) r := by
  have hcast : ((r.val : ℤ) : ZMod (3 ^ (w.length + q))) = r := by simp
  rw [← hcast, finiteTransport_eq_integer, finiteTransport_eq_integer]
  unfold wordTransport
  split_ifs <;> simp [abs_mul, abs_of_pos w.coefficient_pos]

/-- Exact normalized L1 mass, using the proved singleton inverse fiber. -/
theorem finiteMean_abs_finiteTransport (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ) :
    finiteMean (fun r => |finiteTransport w q h r|) =
      w.probability * finiteMean (fun z => |h z|) := by
  have heq : (fun r => |finiteTransport w q h r|) =
      finiteTransport w q (fun z => |h z|) := funext (finiteTransport_abs w q h)
  rw [heq, finiteMean_finiteTransport]

/-- The difference identity used to transport an approximation error. -/
theorem finiteTransport_sub (w : Word) (q : ℕ) (h k : ZMod (3 ^ q) → ℝ)
    (r : ZMod (3 ^ (w.length + q))) :
    finiteTransport w q (fun z => h z - k z) r =
      finiteTransport w q h r - finiteTransport w q k r := by
  classical
  unfold finiteTransport
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> ring

end SyracuseReport
