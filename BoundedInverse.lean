import BoundedInverseArithmetic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.Nat.Totient

/-! Bounded one-step inverse coverage of every unit target by any prescribed
unit cylinder. -/

namespace SyracuseReport

theorem card_units_three_power (q : ℕ) :
    Nat.card (ZMod (3 ^ (q + 1)))ˣ = 2 * 3 ^ q := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_three]
  norm_num
  ring

noncomputable def twoTernaryUnit (q : ℕ) : (ZMod (3 ^ (q + 1)))ˣ :=
  (show IsUnit (2 : ZMod (3 ^ (q + 1))) by
    apply (ZMod.isUnit_iff_coprime _ _).2
    exact (by decide : Nat.Coprime 2 3).pow_right (q + 1)).unit

@[simp] theorem twoTernaryUnit_val (q : ℕ) :
    (twoTernaryUnit q : ZMod (3 ^ (q + 1))) = 2 := by
  unfold twoTernaryUnit
  rw [IsUnit.unit_spec]

theorem twoTernaryUnit_order (q : ℕ) :
    orderOf (twoTernaryUnit q) = Nat.card (ZMod (3 ^ (q + 1)))ˣ := by
  rw [← orderOf_units, twoTernaryUnit_val, orderOf_two_ternary,
    card_units_three_power]

theorem twoTernaryUnit_zpowers (q : ℕ) :
    Subgroup.zpowers (twoTernaryUnit q) = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, twoTernaryUnit_order]

theorem exists_bounded_two_power (q : ℕ) (u : (ZMod (3 ^ (q + 1)))ˣ) :
    ∃ v : ℕ, v < 2 * 3 ^ q ∧ (2 : ZMod (3 ^ (q + 1))) ^ v = u := by
  have hu : u ∈ Subgroup.zpowers (twoTernaryUnit q) := by
    rw [twoTernaryUnit_zpowers]
    exact Subgroup.mem_top u
  rw [mem_zpowers_iff_mem_range_orderOf, twoTernaryUnit_order,
    card_units_three_power] at hu
  obtain ⟨v, hv, hp⟩ := Finset.mem_image.mp hu
  refine ⟨v, Finset.mem_range.mp hv, ?_⟩
  have hp' := congrArg (fun x : (ZMod (3 ^ (q + 1)))ˣ =>
    (x : ZMod (3 ^ (q + 1)))) hp
  simpa only [Units.val_pow_eq_pow_val, twoTernaryUnit_val] using hp'

theorem affineStep_natCast_of_equation (h c : ℕ) (v : ℕ+)
    (r : ZMod (3 ^ (h + 1))) (he : 3 * c + 1 = 2 ^ (v : ℕ) * r.val) :
    affineStep h v (c : ZMod (3 ^ h)) = r := by
  have hm : Nat.ModEq (3 ^ (h + 1)) (3 * (c % 3 ^ h) + 1) (3 * c + 1) := by
    simpa only [pow_succ, Nat.mul_comm] using
      ((Nat.mod_modEq c (3 ^ h)).mul_left' 3).add_right 1
  rw [he] at hm
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have hinner : (3 : ZMod (3 ^ (h + 1))) * (c % 3 ^ h : ℕ) + 1 =
      (2 : ZMod (3 ^ (h + 1))) ^ (v : ℕ) * r := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, ZMod.natCast_zmod_val] using hc
  unfold affineStep
  rw [ZMod.val_natCast, hinner]
  have hi : ((2 : ZMod (3 ^ (h + 1))) ^ (v : ℕ))⁻¹ *
      (2 : ZMod (3 ^ (h + 1))) ^ (v : ℕ) = 1 := by
    rw [mul_comm]
    exact two_power_mul_inv (h + 1) (v : ℕ)
  rw [← mul_assoc, hi, one_mul]

/-- Lemma `bounded-inverse-step` of the manuscript. -/
theorem bounded_inverse_into_cylinder (q h : ℕ) (hqh : q ≤ h)
    (y : ZMod (3 ^ q)) (r : ZMod (3 ^ (h + 1))) (hr : IsUnit r) :
    ∃ (v : ℕ+) (z : ZMod (3 ^ h)),
      (v : ℕ) ≤ 2 * 3 ^ q ∧ residueProjection hqh z = y ∧
        affineStep h v z = r := by
  classical
  letI : NeZero (3 ^ (q + 1)) := ⟨by positivity⟩
  letI : NeZero (3 ^ (h + 1)) := ⟨by positivity⟩
  let rq : ZMod (3 ^ (q + 1)) :=
    residueProjection (Nat.add_le_add_right hqh 1) r
  have hrq : IsUnit rq :=
    (residueProjection_isUnit_iff
      (Nat.add_le_add_right hqh 1) (by omega : 1 ≤ q + 1) r).2 hr
  let A : ZMod (3 ^ (q + 1)) := (3 * y.val + 1 : ℕ)
  have hc : Nat.Coprime (3 * y.val + 1) 3 := by
    rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
    norm_num
  have hA : IsUnit A := by
    apply (ZMod.isUnit_iff_coprime _ _).2
    exact hc.pow_right (q + 1)
  let U : (ZMod (3 ^ (q + 1)))ˣ := hA.unit * (hrq.unit)⁻¹
  obtain ⟨k, hk, hpow⟩ := exists_bounded_two_power q U
  let P := 2 * 3 ^ q
  let V := if k = 0 then P else k
  have hP : 0 < P := by dsimp [P]; positivity
  have hVpos : 0 < V := by
    dsimp [V]
    split_ifs with hzero
    · exact hP
    · omega
  have hVle : V ≤ P := by
    dsimp [V, P]
    split_ifs <;> omega
  have hVpow : (2 : ZMod (3 ^ (q + 1))) ^ V = U := by
    dsimp [V]
    split_ifs with hzero
    · have hU : (1 : ZMod (3 ^ (q + 1))) = U := by
        simpa [hzero] using hpow
      rw [(two_power_eq_one_iff q P).mpr (by dsimp [P]; exact dvd_rfl)]
      exact hU
    · exact hpow
  have htarget : (2 : ZMod (3 ^ (q + 1))) ^ V * rq = A := by
    have hrqspec : (hrq.unit : ZMod (3 ^ (q + 1))) = rq := IsUnit.unit_spec hrq
    rw [hVpow, ← hrqspec]
    change ((U * hrq.unit : (ZMod (3 ^ (q + 1)))ˣ) :
      ZMod (3 ^ (q + 1))) = A
    have hu : U * hrq.unit = hA.unit := by simp [U]
    rw [hu]
    exact IsUnit.unit_spec hA
  have hrqval : rq = (r.val : ZMod (3 ^ (q + 1))) := by
    dsimp [rq]
    simpa only [Int.cast_natCast] using
      residueProjection_val (Nat.add_le_add_right hqh 1) r
  have hcast : ((2 ^ V * r.val : ℕ) : ZMod (3 ^ (q + 1))) =
      ((3 * y.val + 1 : ℕ) : ZMod (3 ^ (q + 1))) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, A, hrqval] using htarget
  have hmod : Nat.ModEq (3 ^ (q + 1)) (2 ^ V * r.val) (3 * y.val + 1) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hrmod : r.val % 3 ≠ 0 :=
    (isUnit_residue_iff (by omega : 1 ≤ h + 1) r).mp hr
  have hrpos : 0 < r.val := by omega
  have hNpos : 1 ≤ 2 ^ V * r.val :=
    Nat.mul_pos (by positivity : 0 < 2 ^ V) hrpos
  have hmod3 : Nat.ModEq 3 (2 ^ V * r.val) (3 * y.val + 1) :=
    hmod.of_dvd (dvd_pow_self 3 (by omega : q + 1 ≠ 0))
  have hmod1 : Nat.ModEq 3 (2 ^ V * r.val) 1 :=
    hmod3.trans Nat.ModEq.modulus_mul_add
  have hdiv : 3 ∣ 2 ^ V * r.val - 1 :=
    (Nat.modEq_iff_dvd' hNpos).mp hmod1.symm
  let c := (2 ^ V * r.val - 1) / 3
  have heq : 3 * c + 1 = 2 ^ V * r.val := by
    have hcancel := Nat.mul_div_cancel' hdiv
    dsimp [c]
    omega
  have hcmod0 : Nat.ModEq (3 ^ (q + 1)) (3 * c + 1) (3 * y.val + 1) := by
    rw [heq]
    exact hmod
  have hcmod1 : Nat.ModEq (3 ^ (q + 1)) (3 * c) (3 * y.val) :=
    Nat.ModEq.add_right_cancel' 1 hcmod0
  have hcmod : Nat.ModEq (3 ^ q) c y.val := by
    have H := hcmod1.cancel_left_div_gcd (by positivity : 0 < 3 ^ (q + 1))
    simpa [pow_succ'] using H
  let v : ℕ+ := ⟨V, hVpos⟩
  let z : ZMod (3 ^ h) := (c : ℤ)
  refine ⟨v, z, hVle, ?_, ?_⟩
  · dsimp [z]
    rw [residueProjection_intCast]
    simp only [Int.cast_natCast]
    rw [← ZMod.natCast_zmod_val y]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcmod
  · have hzNat : z = (c : ZMod (3 ^ h)) := by
      dsimp [z]
      simp only [Int.cast_natCast]
    rw [hzNat]
    apply affineStep_natCast_of_equation h c v r
    change 3 * c + 1 = 2 ^ V * r.val
    exact heq

end SyracuseReport
