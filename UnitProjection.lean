import Cylinder

namespace SyracuseReport
open Filter

theorem isUnit_residue_iff {n : ℕ} (hn : 1 ≤ n) (r : ZMod (3 ^ n)) :
    IsUnit r ↔ r.val % 3 ≠ 0 := by
  have H := ZMod.isUnit_iff_coprime r.val (3 ^ n)
  rw [ZMod.natCast_zmod_val] at H
  rw [Nat.coprime_pow_right_iff (by omega : 0 < n), Nat.coprime_comm,
    Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero] at H
  exact H

theorem residueProjection_isUnit_iff {Q h : ℕ} (hle : h ≤ Q) (hh : 1 ≤ h)
    (z : ZMod (3 ^ Q)) : IsUnit (residueProjection hle z) ↔ IsUnit z := by
  have hv : (residueProjection hle z).val = z.val % (3 ^ h) := by
    have H := congrArg ZMod.val (residueProjection_val hle z)
    simpa only [Int.cast_natCast, ZMod.val_natCast] using H
  rw [isUnit_residue_iff hh, isUnit_residue_iff (hh.trans hle), hv,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : h ≠ 0))]


noncomputable def unitMinorant (c : ℝ) (n : ℕ) (z : ZMod (3 ^ n)) : ℝ := by
  classical
  exact if IsUnit z then (2 / 3 : ℝ) * c else 0

theorem unitMinorant_le_density {c : ℝ} (hF : FloorAt c) {n : ℕ} (hn : 1 ≤ n)
    (z : ZMod (3 ^ n)) : unitMinorant c n z ≤ density n z := by
  classical
  unfold unitMinorant
  split_ifs with hz
  · have hp : (3 : ℝ) ^ n ≠ 0 := by positivity
    calc
      (2 / 3 : ℝ) * c = ((2 / 3 : ℝ) * 3 ^ n) * (c / 3 ^ n) := by field_simp
      _ ≤ ((2 / 3 : ℝ) * 3 ^ n) * (syracuseLaw n z).toReal :=
        mul_le_mul_of_nonneg_left (hF n hn z hz) (by positivity)
      _ = density n z := rfl
  · exact density_nonneg n z

/-- The converse construction of the core estimates, from an atom floor. -/
theorem coreWitness_of_floor {c : ℝ} (hc : 0 < c) (hF : FloorAt c) :
    Nonempty CoreWitness := by
  classical
  refine ⟨{
    depth := id
    approximate := unitMinorant c
    mark := (2 / 3 : ℝ) * c
    excess := 0
    variation := fun _ => 0
    depth_positive := fun _ hj => hj
    depth_tendsto := tendsto_id
    mark_positive := by positivity
    excess_nonnegative := le_rfl
    variation_nonnegative := fun _ _ => le_rfl
    variation_tendsto := tendsto_const_nhds
    positive_mark := ?_
    stabilization := ?_
    mean_excess := ?_ }⟩
  · intro N _
    refine ⟨1, isUnit_one, ?_⟩
    change (2 / 3 : ℝ) * c ≤ unitMinorant c N (1 : ZMod (3 ^ N))
    unfold unitMinorant
    rw [if_pos isUnit_one]
  · intro N j hN _ hle z
    have hu := residueProjection_isUnit_iff hle hN z
    change |unitMinorant c j z - unitMinorant c N (residueProjection hle z)| ≤ 0
    have heq : unitMinorant c j z = unitMinorant c N (residueProjection hle z) := by
      unfold unitMinorant
      exact if_congr hu.symm rfl rfl
    rw [heq, sub_self, abs_zero]
  · intro j hj
    have heq : (fun z => max (unitMinorant c j z - density j z) 0) =
        (fun _ : ZMod (3 ^ j) => (0 : ℝ)) := by
      funext z
      exact max_eq_right (sub_nonpos.mpr (unitMinorant_le_density hF hj z))
    change finiteMean (fun z => max (unitMinorant c j z - density j z) 0) ≤ 0 / (j : ℝ)
    rw [heq]
    simp only [finiteMean, Finset.sum_const_zero, zero_div, le_refl]

end SyracuseReport
