import UnitProjection
import Mathlib.NumberTheory.Multiplicity
import Mathlib.GroupTheory.OrderOfElement

/-! The element two has the full unit-group order modulo every positive
power of three. This is the arithmetic input to bounded inverse coverage. -/

namespace SyracuseReport

theorem three_power_dvd_four_power_sub_one (q n : ℕ) :
    3 ^ (q + 1) ∣ 4 ^ n - 1 ↔ 3 ^ q ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn4 : 4 ^ n - 1 ≠ 0 := by
    have H : 1 < (4 : ℕ) ^ n := one_lt_pow₀ (by decide) hn
    omega
  have hv := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide : Odd 3) (by decide : 1 < (4 : ℕ))
    (by decide : 3 ∣ 4 - 1) (by decide : ¬3 ∣ 4) hn
  simp only [one_pow] at hv
  have hself : padicValNat 3 (4 - 1) = 1 := by norm_num
  rw [hself] at hv
  rw [padicValNat_dvd_iff_le hn4, padicValNat_dvd_iff_le hn, hv]
  omega

theorem two_power_eq_one_iff (q n : ℕ) :
    (2 : ZMod (3 ^ (q + 1))) ^ n = 1 ↔ 2 * 3 ^ q ∣ n := by
  have heq : (2 : ZMod (3 ^ (q + 1))) ^ n = 1 ↔
      3 ^ (q + 1) ∣ 2 ^ n - 1 := by
    have hcast : ((2 ^ n - 1 : ℕ) : ZMod (3 ^ (q + 1))) =
        (2 : ZMod (3 ^ (q + 1))) ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [← sub_eq_zero, ← hcast, ZMod.natCast_eq_zero_iff]
  constructor
  · intro hp
    have h3 := congrArg (residueProjection (by omega : 1 ≤ q + 1)) hp
    simp only [map_pow, map_ofNat, map_one] at h3
    have htwo : (2 : ZMod 3) = -1 := by decide
    change (2 : ZMod 3) ^ n = 1 at h3
    rw [htwo, neg_one_pow_eq_one_iff_even
      (by decide : (-1 : ZMod 3) ≠ 1)] at h3
    obtain ⟨t, ht⟩ := h3
    have hn : n = 2 * t := by omega
    have hdiv := heq.mp hp
    rw [hn, pow_mul] at hdiv
    norm_num at hdiv
    have ht3 := (three_power_dvd_four_power_sub_one q t).mp hdiv
    rw [hn]
    exact Nat.mul_dvd_mul_left 2 ht3
  · rintro ⟨t, rfl⟩
    apply heq.mpr
    have hh := (three_power_dvd_four_power_sub_one q (3 ^ q * t)).mpr
      (dvd_mul_right _ _)
    convert hh using 1
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
    congr 1
    ring

theorem orderOf_two_ternary (q : ℕ) :
    orderOf (2 : ZMod (3 ^ (q + 1))) = 2 * 3 ^ q := by
  apply (orderOf_eq_iff (by positivity : 0 < 2 * 3 ^ q)).mpr
  refine ⟨(two_power_eq_one_iff q _).mpr dvd_rfl, ?_⟩
  intro m hm hm0 he
  exact Nat.not_dvd_of_pos_of_lt hm0 hm ((two_power_eq_one_iff q m).mp he)

end SyracuseReport
