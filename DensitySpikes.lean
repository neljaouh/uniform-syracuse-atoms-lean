import UnitDensitySteps
import BoundedInverse

/-! Explicit density spikes in every unit residue cylinder.
Only finite affine maps and their arithmetic projection identities are used. -/
namespace SyracuseReport

theorem affineStep_intCast (n : ℕ) (a : ℕ+) (z : ℤ) :
    affineStep n a (z : ZMod (3 ^ n)) =
      ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * (3 * z + 1) := by
  have he : (3 : ZMod (3 ^ (1 + n))) ^ 1 *
      (((z : ZMod (3 ^ n)).val : ℤ)) =
      (3 : ZMod (3 ^ (1 + n))) ^ 1 * z := by
    apply (scaled_int_cast_eq_iff 1 n _ _).mpr
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have he' : (3 : ZMod (3 ^ (n + 1))) *
      (z : ZMod (3 ^ n)).val = 3 * (z : ZMod (3 ^ (n + 1))) := by
    rw [Nat.add_comm 1 n, pow_one] at he
    simpa only [Int.cast_natCast] using he
  unfold affineStep
  rw [he']

theorem affineStep_one_neg_one (n : ℕ) :
    affineStep n 1 (-1) = (-1 : ZMod (3 ^ (n + 1))) := by
  have h := affineStep_intCast n 1 (-1)
  simp only [Int.cast_neg, Int.cast_one, PNat.val_ofNat, pow_one] at h
  rw [h]
  have hi : (2 : ZMod (3 ^ (n + 1)))⁻¹ * 2 = 1 := by
    rw [mul_comm]
    simpa using two_power_mul_inv (n + 1) 1
  calc
    _ = -(2⁻¹ * (2 : ZMod (3 ^ (n + 1)))) := by ring
    _ = -1 := by rw [hi]

theorem neg_one_density_lower (n : ℕ) :
    (2 / 3 : ℝ) * (3 / 2 : ℝ) ^ n ≤ density n (-1) := by
  induction n with
  | zero =>
      have h : (-1 : ZMod (3 ^ 0)) = 0 := by
        change (-1 : ZMod 1) = 0
        exact Subsingleton.elim _ _
      simp [h, density, syracuseLaw]
  | succ n ih =>
      have hstep := density_one_step n 1 (-1) (-1) (affineStep_one_neg_one n)
      norm_num only [PNat.val_ofNat, pow_one] at hstep
      have hmul := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 3 / 2)
      rw [pow_succ]
      nlinarith

theorem exists_affine_neg_one (q : ℕ) (r : ZMod (3 ^ (q + 1))) (hr : IsUnit r) :
    ∃ a : ℕ+, affineStep q a (-1) = r := by
  let u : (ZMod (3 ^ (q + 1)))ˣ := -(twoTernaryUnit q) * hr.unit⁻¹
  obtain ⟨v, _, hv⟩ := exists_bounded_two_power q u
  let P := 2 * 3 ^ q
  let a : ℕ+ := ⟨v + P, by dsimp [P]; positivity⟩
  have hP : (2 : ZMod (3 ^ (q + 1))) ^ P = 1 :=
    (two_power_eq_one_iff q P).mpr dvd_rfl
  have ha : (2 : ZMod (3 ^ (q + 1))) ^ (a : ℕ) = u := by
    change (2 : ZMod (3 ^ (q + 1))) ^ (v + P) = _
    calc
      (2 : ZMod (3 ^ (q + 1))) ^ (v + P) =
          (2 : ZMod (3 ^ (q + 1))) ^ v * 2 ^ P := pow_add _ _ _
      _ = (2 : ZMod (3 ^ (q + 1))) ^ v := by rw [hP, mul_one]
      _ = u := hv
  have hmul : (2 : ZMod (3 ^ (q + 1))) ^ (a : ℕ) * r = -2 := by
    rw [ha, ← IsUnit.unit_spec hr]
    change ((u * hr.unit : (ZMod (3 ^ (q + 1)))ˣ) :
      ZMod (3 ^ (q + 1))) = -2
    have he : u * hr.unit = -(twoTernaryUnit q) := by simp [u]
    rw [he]
    simp only [Units.val_neg, twoTernaryUnit_val]
  refine ⟨a, ?_⟩
  have hform := affineStep_intCast q a (-1)
  simp only [Int.cast_neg, Int.cast_one] at hform
  rw [hform]
  have hi := two_power_mul_inv (q + 1) (a : ℕ)
  have hi' : ((2 : ZMod (3 ^ (q + 1))) ^ (a : ℕ))⁻¹ * 2 ^ (a : ℕ) = 1 := by
    rwa [mul_comm]
  have he : (3 : ZMod (3 ^ (q + 1))) * (-1) + 1 = -2 := by ring
  rw [he, ← hmul, ← mul_assoc, hi', one_mul]

theorem large_density_in_cylinder (q : ℕ) (hq : 1 ≤ q)
    (r : ZMod (3 ^ q)) (hr : IsUnit r) (M : ℝ) :
    ∃ (n : ℕ) (hqn : q ≤ n) (s : ZMod (3 ^ n)),
      IsUnit s ∧ residueProjection hqn s = r ∧ M < density n s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  obtain ⟨a, ha⟩ := exists_affine_neg_one k r hr
  let c : ℝ := 2 / (2 : ℝ) ^ (a : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / c)
  let n := max k N
  have hkn : k ≤ n := le_max_left _ _
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_max_right k N
  have hMn : M < c * (n : ℝ) / 2 := by
    have h := (div_lt_iff₀ hc).mp hN
    have hm := mul_le_mul_of_nonneg_left hNn hc.le
    nlinarith
  let s := affineStep n a (-1)
  have hproj : residueProjection (Nat.add_le_add_right hkn 1) s = r := by
    rw [affineStep_project hkn]
    simpa only [map_neg, map_one] using ha
  have hs : IsUnit s :=
    (residueProjection_isUnit_iff (Nat.add_le_add_right hkn 1) (by omega) s).mp
      (by rw [hproj]; exact hr)
  have hstep := density_one_step n a (-1) s rfl
  have hbase := neg_one_density_lower n
  have hbound : c * (3 / 2 : ℝ) ^ n ≤ density (n + 1) s := by
    have h := mul_le_mul_of_nonneg_left hbase
      (by positivity : (0 : ℝ) ≤ 3 / (2 : ℝ) ^ (a : ℕ))
    have he : (3 / (2 : ℝ) ^ (a : ℕ)) *
        ((2 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) = c * (3 / 2 : ℝ) ^ n := by
      dsimp [c]
      ring
    rw [he] at h
    exact h.trans hstep
  have hpower : 1 + (n : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ n := by
    convert (one_add_mul_le_pow (a := (1 / 2 : ℝ)) (by norm_num) n) using 1 <;> ring
  have hlarge : M < density (n + 1) s := by
    have h := mul_le_mul_of_nonneg_left hpower hc.le
    linarith
  exact ⟨n + 1, Nat.add_le_add_right hkn 1, s, hs, hproj, hlarge⟩

end SyracuseReport
