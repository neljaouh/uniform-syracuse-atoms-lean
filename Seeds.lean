import BoundedInverseArithmetic
import BoundedInverse

/-! Integer seed construction for an arbitrary signed Collatz target. -/

namespace SyracuseReport

@[simp] theorem collatz_two_mul (m : ℤ) : collatz (2 * m) = m := by
  simp [collatz]

theorem iterate_collatz_two_pow (a : ℤ) (n : ℕ) :
    collatz^[n] ((2 : ℤ) ^ n * a) = a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, pow_succ']
      simp only [mul_assoc, collatz_two_mul]
      exact ih

theorem collatz_odd_step {R a : ℤ} {k : ℕ} (hk : 1 ≤ k) (hR : Odd R)
    (heq : 3 * R + 1 = (2 : ℤ) ^ k * a) :
    collatz R = (2 : ℤ) ^ (k - 1) * a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hmod : R % 2 ≠ 0 := by
    rw [Int.odd_iff] at hR
    omega
  simp only [collatz, hmod, ite_false]
  rw [heq]
  simp only [pow_succ', Nat.succ_sub_one]
  rw [mul_assoc, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

theorem reaches_of_seed_equation {R a : ℤ} {k : ℕ} (hk : 1 ≤ k) (hR : Odd R)
    (heq : 3 * R + 1 = (2 : ℤ) ^ k * a) : Reaches R a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply, collatz_odd_step (by omega) hR heq]
  simpa using iterate_collatz_two_pow a n

/-- In every ternary residue class there are arbitrarily large odd seeds
which reach a prescribed target prime to three and have its sign. -/
theorem signed_seed_in_residue (a : ℤ) (ha : ¬(3 : ℤ) ∣ a) (q : ℕ) (hq : 1 ≤ q)
    (y : ZMod (3 ^ q)) (B : ℕ) :
    ∃ R : ℤ, Odd R ∧ (R : ZMod (3 ^ q)) = y ∧ Reaches R a ∧
      0 < a * R ∧ (B : ℤ) < |R| := by
  have ha3 : IsUnit (a : ZMod 3) :=
    (CharP.isUnit_intCast_iff (R := ZMod 3) (by decide)).2 ha
  have haQ : IsUnit (a : ZMod (3 ^ (q + 1))) := by
    apply (residueProjection_isUnit_iff (Q := q + 1) (h := 1) (by omega) (by omega)
      (a : ZMod (3 ^ (q + 1)))).mp
    simpa only [residueProjection_intCast] using ha3
  obtain ⟨v, z, hv, hzy, hz⟩ :=
    bounded_inverse_into_cylinder q q le_rfl y (a : ZMod (3 ^ (q + 1))) haQ
  let period : ℕ := 2 * 3 ^ q
  let T : ℕ := 3 * B + 3
  let k : ℕ := (v : ℕ) + period * T
  have hk : 1 ≤ k := by
    dsimp [k]
    exact v.pos.trans_le (Nat.le_add_right _ _)
  have hperiod : (2 : ZMod (3 ^ (q + 1))) ^ period = 1 := by
    apply (two_power_eq_one_iff q period).2
    exact dvd_rfl
  have hpow : (2 : ZMod (3 ^ (q + 1))) ^ k =
      (2 : ZMod (3 ^ (q + 1))) ^ (v : ℕ) := by
    have hpT : (2 : ZMod (3 ^ (q + 1))) ^ (period * T) = 1 := by
      rw [pow_mul, hperiod, one_pow]
    calc
      (2 : ZMod (3 ^ (q + 1))) ^ k =
          (2 : ZMod (3 ^ (q + 1))) ^ (v : ℕ) *
            (2 : ZMod (3 ^ (q + 1))) ^ (period * T) := by
              rw [show k = (v : ℕ) + period * T by rfl]
              exact pow_add _ _ _
      _ = _ := by rw [hpT, mul_one]
  have hscale := affineStep_scaled q v z
  rw [hz] at hscale
  have hcong : (2 : ZMod (3 ^ (q + 1))) ^ k * (a : ZMod (3 ^ (q + 1))) =
      3 * z.val + 1 := by
    rw [hpow]
    exact hscale
  let N : ℤ := (2 : ℤ) ^ k * a - 1
  have hcast : (((2 : ℤ) ^ k * a : ℤ) : ZMod (3 ^ (q + 1))) =
      (((3 : ℤ) * z.val + 1 : ℤ) : ZMod (3 ^ (q + 1))) := by
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_add, Int.cast_one] using hcong
  have hdivHigh : ((3 : ℤ) ^ (q + 1)) ∣
      ((3 : ℤ) * z.val + 1) - (2 : ℤ) ^ k * a := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have hthreePow : (3 : ℤ) ∣ (3 : ℤ) ^ (q + 1) := by
    exact dvd_pow_self 3 (by omega : q + 1 ≠ 0)
  have hdivDiff : (3 : ℤ) ∣
      ((3 : ℤ) * z.val + 1) - (2 : ℤ) ^ k * a :=
    dvd_trans hthreePow hdivHigh
  have hdivN : (3 : ℤ) ∣ N := by
    rw [show N = (3 : ℤ) * z.val -
        (((3 : ℤ) * z.val + 1) - (2 : ℤ) ^ k * a) by
      dsimp [N]
      ring]
    exact dvd_sub (dvd_mul_right (3 : ℤ) (z.val : ℤ)) hdivDiff
  let R : ℤ := N / 3
  have hseed : 3 * R + 1 = (2 : ℤ) ^ k * a := by
    have hcancel := Int.ediv_mul_cancel hdivN
    dsimp [R]
    rw [mul_comm 3 (N / 3), hcancel]
    dsimp [N]
    ring
  have hRodd : Odd R := by
    apply ZMod.intCast_eq_one_iff_odd.mp
    have htwo : (2 : ZMod 2) ^ k = 0 := by
      have hbase : (2 : ZMod 2) = 0 := by decide
      rw [hbase, zero_pow (by omega : k ≠ 0)]
    have hc := congrArg (fun x : ℤ => (x : ZMod 2)) hseed
    push_cast at hc
    rw [htwo, zero_mul] at hc
    have hthree : (3 : ZMod 2) = 1 := by decide
    rw [hthree, one_mul] at hc
    have hneg : (-(1 : ZMod 2)) = 1 := by decide
    rw [← hneg]
    exact eq_neg_of_add_eq_zero_left hc
  have hRz : (R : ZMod (3 ^ q)) = z := by
    have hRval : (R : ZMod (3 ^ q)) = ((z.val : ℤ) : ZMod (3 ^ q)) := by
      apply (scaled_int_cast_eq_iff 1 q R z.val).mp
      have hscaled :
          (3 : ZMod (3 ^ (q + 1))) * (R : ZMod (3 ^ (q + 1))) =
            (3 : ZMod (3 ^ (q + 1))) * (z.val : ZMod (3 ^ (q + 1))) := by
        calc
        (3 : ZMod (3 ^ (q + 1))) * (R : ZMod (3 ^ (q + 1))) =
            (2 : ZMod (3 ^ (q + 1))) ^ k * (a : ZMod (3 ^ (q + 1))) - 1 := by
              have hc := congrArg (fun x : ℤ => (x : ZMod (3 ^ (q + 1)))) hseed
              push_cast at hc
              linear_combination hc
        _ = (3 : ZMod (3 ^ (q + 1))) * (z.val : ZMod (3 ^ (q + 1))) := by
              rw [hcong]
              ring
      rw [Nat.add_comm 1 q]
      simpa only [pow_one, Int.cast_natCast] using hscaled
    simpa using hRval
  refine ⟨R, hRodd, ?_, reaches_of_seed_equation hk hRodd hseed, ?_, ?_⟩
  · calc
      (R : ZMod (3 ^ q)) = z := hRz
      _ = residueProjection le_rfl z := by
        rw [residueProjection_val]
        simp
      _ = y := hzy
  · have ha0 : a ≠ 0 := by
      intro haz
      subst a
      exact ha (dvd_zero 3)
    have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
    have hpowLower : (1 : ℤ) + k ≤ (2 : ℤ) ^ k := by
      simpa using (one_add_mul_le_pow (a := (1 : ℤ)) (by omega) k)
    have hpowTwo : (2 : ℤ) ≤ (2 : ℤ) ^ k := by omega
    rcases lt_or_gt_of_ne ha0 with haNeg | haPos
    · have hRneg : R < 0 := by
        have haOne : a ≤ -1 := by omega
        have hpNonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
        have hmul : (2 : ℤ) ^ k * a ≤ -(2 : ℤ) ^ k := by
          nlinarith [mul_le_mul_of_nonneg_left haOne hpNonneg]
        nlinarith
      exact mul_pos_of_neg_of_neg haNeg hRneg
    · have hRpos : 0 < R := by
        have haOne : 1 ≤ a := by omega
        have hpNonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
        have hmul : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ k * a := by
          nlinarith [mul_le_mul_of_nonneg_left haOne hpNonneg]
        nlinarith
      exact mul_pos haPos hRpos
  · have hpPeriod : 1 ≤ period := by
      dsimp [period]
      have h3 : 0 < 3 ^ q := pow_pos (by omega) q
      omega
    have hTk : T ≤ k := by
      calc
        T = 1 * T := by simp
        _ ≤ period * T := Nat.mul_le_mul_right T hpPeriod
        _ ≤ (v : ℕ) + period * T := Nat.le_add_left _ _
        _ = k := rfl
    have hkB : 3 * B + 3 ≤ k := by simpa only [T] using hTk
    have hkBz : 3 * (B : ℤ) + 3 ≤ (k : ℤ) := by exact_mod_cast hkB
    have hpowLower : (1 : ℤ) + k ≤ (2 : ℤ) ^ k := by
      simpa using (one_add_mul_le_pow (a := (1 : ℤ)) (by omega) k)
    have hpNonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    have ha0 : a ≠ 0 := by
      intro haz
      subst a
      exact ha (dvd_zero 3)
    rcases lt_or_gt_of_ne ha0 with haNeg | haPos
    · have hminusA : 1 ≤ -a := by omega
      have hmul : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ k * (-a) := by
        nlinarith [mul_le_mul_of_nonneg_left hminusA hpNonneg]
      have hRneg : R < 0 := by
        have hp : 0 < (2 : ℤ) ^ k := by positivity
        nlinarith [mul_neg_of_pos_of_neg hp haNeg]
      rw [abs_of_neg hRneg]
      nlinarith
    · have haOne : 1 ≤ a := by omega
      have hmul : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ k * a := by
        nlinarith [mul_le_mul_of_nonneg_left haOne hpNonneg]
      have hRpos : 0 < R := by
        have hp : 0 < (2 : ℤ) ^ k := by positivity
        nlinarith [mul_pos hp haPos]
      rw [abs_of_pos hRpos]
      nlinarith

end SyracuseReport
