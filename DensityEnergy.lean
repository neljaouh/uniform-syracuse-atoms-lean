import Stationarity
import LawIdentification

/-! Finite collision energy for the actual Syracuse laws.

The algebraic step is a finite affine energy balance, independent of the
Syracuse law, the ternary modulus, and geometric probabilities. The local
memoryless law supplies its specialization below.

This file uses the paper's local law and unit-Haar normalization. The
general finite balance and its Syracuse specialization are proved below;
no historical priority claim is made for the specialized identity.
-/
namespace SyracuseReport
open scoped BigOperators ENNReal

section FiniteEnergyBalance

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Pair a function with the mass injected by a finite map. No injectivity
is needed for this finite change of summation order. -/
theorem finite_injection_pairing (e : ι → κ) (v : ι → ℝ) (u : κ → ℝ) :
    (∑ y : κ, u y * ∑ x : ι, if e x = y then v x else 0) =
      ∑ x : ι, u (e x) * v x := by
  classical
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- An injective placement of finite masses preserves their quadratic sum. -/
theorem finite_injection_square_sum (e : ι → κ) (he : Function.Injective e)
    (v : ι → ℝ) :
    (∑ y : κ, (∑ x : ι, if e x = y then v x else 0) ^ 2) =
      ∑ x : ι, v x ^ 2 := by
  classical
  simp_rw [pow_two]
  rw [finite_injection_pairing]
  simp [he.eq_iff]

/-- A permutation recurrence with an injected boundary mass has an exact
quadratic balance. The coefficients may be arbitrary real numbers. -/
theorem finite_affine_energy_balance (σ : κ ≃ κ)
    (e : ι → κ) (he : Function.Injective e)
    (u : κ → ℝ) (v : ι → ℝ) (a b : ℝ)
    (hstep : ∀ y, u (σ y) = a * u y + b * ∑ x : ι, if e x = y then v x else 0) :
    (1 - a ^ 2) * (∑ y : κ, u y ^ 2) =
      b ^ 2 * (∑ x : ι, v x ^ 2) +
        2 * a * b * (∑ x : ι, u (e x) * v x) := by
  classical
  have hperm : (∑ y : κ, u (σ y) ^ 2) = ∑ y : κ, u y ^ 2 :=
    Equiv.sum_comp σ (fun y => u y ^ 2)
  have hlocal (y : κ) :
      u (σ y) ^ 2 = a ^ 2 * u y ^ 2 +
        b ^ 2 * (∑ x : ι, if e x = y then v x else 0) ^ 2 +
        (2 * a * b) * (u y * ∑ x : ι, if e x = y then v x else 0) := by
    rw [hstep]
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun y _ => hlocal y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hperm,
    finite_injection_square_sum e he, finite_injection_pairing] at hsum
  nlinarith [hsum]

end FiniteEnergyBalance

noncomputable def atomMass (n : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  (syracuseLaw n r).toReal

noncomputable def ternaryLift (n : ℕ) (z : ZMod (3 ^ n)) :
    ZMod (3 ^ (n + 1)) := 3 * z.val + 1

noncomputable def binaryHalf (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    ZMod (3 ^ (n + 1)) := 2⁻¹ * r

theorem binaryHalf_injective (n : ℕ) : Function.Injective (binaryHalf n) := by
  intro r s hrs
  have h := congrArg (fun x : ZMod (3 ^ (n + 1)) => 2 * x) hrs
  have hi : (2 : ZMod (3 ^ (n + 1))) * 2⁻¹ = 1 := by
    simpa using two_power_mul_inv (n + 1) 1
  simpa only [binaryHalf, ← mul_assoc, hi, one_mul] using h

theorem affineStep_first (n : ℕ) (z : ZMod (3 ^ n)) :
    affineStep n 1 z = binaryHalf n (ternaryLift n z) := by
  simp [affineStep, binaryHalf, ternaryLift]

theorem affineStep_next (n : ℕ) (z : ZMod (3 ^ n)) (a : ℕ+) :
    affineStep n (a + 1) z = binaryHalf n (affineStep n a z) := by
  have hinv :
      ((2 : ZMod (3 ^ (n + 1))) ^ ((a + 1 : ℕ+) : ℕ))⁻¹ =
        2⁻¹ * ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    simp only [PNat.add_coe, PNat.val_ofNat, pow_succ]
    have hi := two_power_mul_inv (n + 1) (a : ℕ)
    have hi2 : (2 : ZMod (3 ^ (n + 1))) * 2⁻¹ = 1 := by
      simpa using two_power_mul_inv (n + 1) 1
    calc
      _ = ((2 : ZMod (3 ^ (n + 1))) * 2⁻¹) *
          ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) *
            ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) := by ring
      _ = 1 := by rw [hi, hi2]; ring
  simp only [affineStep, binaryHalf, hinv]
  ring

theorem ternaryLift_injective (n : ℕ) : Function.Injective (ternaryLift n) := by
  intro z z' h
  have he : (3 : ZMod (3 ^ (1 + n))) ^ 1 * (z.val : ℤ) =
      (3 : ZMod (3 ^ (1 + n))) ^ 1 * (z'.val : ℤ) := by
    have hh : (3 : ZMod (3 ^ (n + 1))) * z.val =
        (3 : ZMod (3 ^ (n + 1))) * z'.val := by
      exact add_right_cancel h
    rw [Nat.add_comm 1 n, pow_one]
    exact_mod_cast hh
  have hz := (scaled_int_cast_eq_iff 1 n z.val z'.val).mp he
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz

noncomputable def branchAtom (n : ℕ) (r : ZMod (3 ^ (n + 1)))
    (z : ZMod (3 ^ n)) (a : ℕ+) : ℝ :=
  if affineStep n a z = r then (letterLaw a).toReal * atomMass n z else 0

theorem summable_branchAtom (n : ℕ) (r : ZMod (3 ^ (n + 1)))
    (z : ZMod (3 ^ n)) : Summable (branchAtom n r z) := by
  have hs : Summable (fun a : ℕ+ => (letterLaw a).toReal) := by
    apply ENNReal.summable_toReal
    rw [letterLaw.tsum_coe]
    exact ENNReal.one_ne_top
  apply (hs.mul_right (atomMass n z)).of_nonneg_of_le
  · intro a
    unfold branchAtom atomMass
    split_ifs <;> positivity
  · intro a
    unfold branchAtom
    split_ifs
    · exact le_rfl
    · unfold atomMass
      positivity

theorem atomMass_recursion (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    atomMass (n + 1) r = ∑ z : ZMod (3 ^ n), ∑' a : ℕ+, branchAtom n r z a := by
  classical
  have hfinite (a : ℕ+) :
      (∑ z : ZMod (3 ^ n),
        if affineStep n a z = r then syracuseLaw n z else 0) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro z _
    split_ifs
    · exact (syracuseLaw n).apply_ne_top z
    · exact ENNReal.zero_ne_top
  unfold atomMass
  rw [syracuseLaw_recursion, ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.toReal_mul]
    have hterm (a : ℕ+) :
        (letterLaw a).toReal *
          (∑ z : ZMod (3 ^ n), if affineStep n a z = r then syracuseLaw n z else 0).toReal =
        ∑ z : ZMod (3 ^ n), branchAtom n r z a := by
      rw [ENNReal.toReal_sum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        unfold branchAtom atomMass
        split_ifs <;> simp
      · intro z _
        split_ifs
        · exact (syracuseLaw n).apply_ne_top z
        · exact ENNReal.zero_ne_top
    simp_rw [hterm]
    exact Summable.tsum_finsetSum (fun z _ => summable_branchAtom n r z)
  · intro a
    exact ENNReal.mul_ne_top (letterLaw.apply_ne_top a) (hfinite a)

theorem letterLaw_next (a : ℕ+) :
    (letterLaw (a + 1)).toReal = (letterLaw a).toReal / 2 := by
  rw [letterLaw_real, letterLaw_real]
  simp only [PNat.add_coe, PNat.val_ofNat, pow_succ]
  ring

theorem branchAtom_next (n : ℕ) (r : ZMod (3 ^ (n + 1)))
    (z : ZMod (3 ^ n)) (a : ℕ+) :
    branchAtom n (binaryHalf n r) z (a + 1) = branchAtom n r z a / 2 := by
  have hiff : affineStep n (a + 1) z = binaryHalf n r ↔ affineStep n a z = r := by
    rw [affineStep_next]
    exact (binaryHalf_injective n).eq_iff
  unfold branchAtom
  rw [if_congr hiff rfl rfl]
  split_ifs <;> simp only [letterLaw_next, zero_div] <;> ring

theorem branchAtom_first (n : ℕ) (r : ZMod (3 ^ (n + 1)))
    (z : ZMod (3 ^ n)) :
    branchAtom n (binaryHalf n r) z 1 =
      (if ternaryLift n z = r then atomMass n z else 0) / 2 := by
  have hiff : affineStep n 1 z = binaryHalf n r ↔ ternaryLift n z = r := by
    rw [affineStep_first]
    exact (binaryHalf_injective n).eq_iff
  unfold branchAtom
  rw [if_congr hiff rfl rfl]
  split_ifs <;> simp [letterLaw_real] <;> ring

theorem tsum_positive_first {f : ℕ+ → ℝ} (hf : Summable f) :
    ∑' a, f a = f 1 + ∑' a : ℕ+, f (a + 1) := by
  have hs := Equiv.pnatEquivNat.symm.summable_iff.mpr hf
  have h := hs.tsum_eq_zero_add
  have h0 := Equiv.pnatEquivNat.symm.tsum_eq f
  have h1 := Equiv.pnatEquivNat.symm.tsum_eq (fun a : ℕ+ => f (a + 1))
  simpa only [Equiv.pnatEquivNat_symm_apply, ← h0, ← h1] using h

noncomputable def injectedAtom (n : ℕ) (r : ZMod (3 ^ (n + 1))) : ℝ :=
  ∑ z : ZMod (3 ^ n), if ternaryLift n z = r then atomMass n z else 0

theorem atomMass_memoryless (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    atomMass (n + 1) (binaryHalf n r) =
      (atomMass (n + 1) r + injectedAtom n r) / 2 := by
  have h (z : ZMod (3 ^ n)) :
      (∑' a, branchAtom n (binaryHalf n r) z a) =
        ((∑' a, branchAtom n r z a) +
          if ternaryLift n z = r then atomMass n z else 0) / 2 := by
    rw [tsum_positive_first (summable_branchAtom n (binaryHalf n r) z),
      branchAtom_first]
    simp_rw [branchAtom_next]
    rw [tsum_div_const]
    ring
  rw [atomMass_recursion]
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← atomMass_recursion]
  rfl

theorem injectedAtom_lift (n : ℕ) (z : ZMod (3 ^ n)) :
    injectedAtom n (ternaryLift n z) = atomMass n z := by
  classical
  simp [injectedAtom, (ternaryLift_injective n).eq_iff]

theorem sum_mul_injectedAtom (n : ℕ) (f : ZMod (3 ^ (n + 1)) → ℝ) :
    (∑ r, f r * injectedAtom n r) =
      ∑ z : ZMod (3 ^ n), f (ternaryLift n z) * atomMass n z := by
  classical
  simp only [injectedAtom, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

noncomputable def collisionEnergy (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) * (3 : ℝ) ^ n *
    ∑ r : ZMod (3 ^ n), (atomMass n r) ^ 2

theorem collisionEnergy_recurrence (n : ℕ) :
    collisionEnergy (n + 1) = collisionEnergy n +
      (4 / 3 : ℝ) * (3 : ℝ) ^ n *
        ∑ z : ZMod (3 ^ n),
          atomMass (n + 1) (ternaryLift n z) * atomMass n z := by
  classical
  let σ : ZMod (3 ^ (n + 1)) ≃ ZMod (3 ^ (n + 1)) :=
    Equiv.ofBijective (binaryHalf n)
      ⟨binaryHalf_injective n, Finite.surjective_of_injective (binaryHalf_injective n)⟩
  have hstep (r : ZMod (3 ^ (n + 1))) :
      atomMass (n + 1) (σ r) =
        (1 / 2 : ℝ) * atomMass (n + 1) r +
        (1 / 2 : ℝ) * ∑ z : ZMod (3 ^ n),
          if ternaryLift n z = r then atomMass n z else 0 := by
    change atomMass (n + 1) (binaryHalf n r) = _
    rw [atomMass_memoryless]
    unfold injectedAtom
    ring
  have hbalance := finite_affine_energy_balance σ (ternaryLift n)
    (ternaryLift_injective n) (atomMass (n + 1)) (atomMass n) (1 / 2) (1 / 2) hstep
  norm_num only [one_div, inv_pow, one_pow] at hbalance
  unfold collisionEnergy
  rw [pow_succ]
  have hscaled := congrArg (fun x : ℝ => (3 : ℝ) ^ n * x) hbalance
  nlinarith [hscaled]

theorem ternaryLift_isUnit (n : ℕ) (z : ZMod (3 ^ n)) :
    IsUnit (ternaryLift n z) := by
  have hc : Nat.Coprime (3 * z.val + 1) 3 := by
    simp [Nat.coprime_mul_left_add_left]
  have hu := (ZMod.isUnit_iff_coprime (3 * z.val + 1) (3 ^ (n + 1))).mpr
    (hc.pow_right (n + 1))
  simpa [ternaryLift] using hu

theorem collisionEnergy_gain {c : ℝ} (hf : FloorAt c) (n : ℕ) :
    collisionEnergy n + 4 * c / 9 ≤ collisionEnergy (n + 1) := by
  have hsum : c / (3 : ℝ) ^ (n + 1) ≤
      ∑ z : ZMod (3 ^ n),
        atomMass (n + 1) (ternaryLift n z) * atomMass n z := by
    calc
      c / (3 : ℝ) ^ (n + 1) =
          ∑ z : ZMod (3 ^ n), c / (3 : ℝ) ^ (n + 1) * atomMass n z := by
            rw [← Finset.mul_sum]
            change _ = _ * (∑ z, (syracuseLaw n z).toReal)
            rw [syracuseLaw_real_sum, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_right
          (hf (n + 1) (by omega) (ternaryLift n z) (ternaryLift_isUnit n z))
          ENNReal.toReal_nonneg)
  have h := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (4 / 3 : ℝ) * 3 ^ n by positivity)
  have he : (4 / 3 : ℝ) * (3 : ℝ) ^ n * (c / (3 : ℝ) ^ (n + 1)) = 4 * c / 9 := by
    rw [pow_succ]
    field_simp
    <;> ring
  rw [he] at h
  rw [collisionEnergy_recurrence]
  linarith

theorem collisionEnergy_one : collisionEnergy 1 = 10 / 9 := by
  classical
  unfold collisionEnergy
  rw [pow_one]
  change (2 / 3 : ℝ) * 3 * (∑ r : Fin 3, atomMass 1 r ^ 2) = 10 / 9
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 / 3 : ℝ) * 3 *
    (atomMass 1 0 ^ 2 + (atomMass 1 1 ^ 2 + atomMass 1 2 ^ 2)) = 10 / 9
  norm_num [atomMass, syracuseLaw_eq_syracPMF,
    Erdos1135.Tao.syracPMF_one_apply_zero,
    Erdos1135.Tao.syracPMF_one_apply_one,
    Erdos1135.Tao.syracPMF_one_apply_two]

theorem collisionEnergy_linear {c : ℝ} (hf : FloorAt c) (n : ℕ) (hn : 1 ≤ n) :
    10 / 9 + (4 * c / 9) * ((n - 1 : ℕ) : ℝ) ≤ collisionEnergy n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  induction k with
  | zero => simp [collisionEnergy_one]
  | succ k ih =>
      have h := collisionEnergy_gain hf (k + 1)
      have hih := ih (by omega)
      push_cast
      change 10 / 9 + (4 * c / 9) * ((k : ℝ) + 1) ≤ collisionEnergy ((k + 1) + 1)
      linarith

theorem collisionEnergy_unbounded {c : ℝ} (hc : 0 < c) (hf : FloorAt c) :
    ∀ M : ℝ, ∃ n : ℕ, 1 ≤ n ∧ M < collisionEnergy n := by
  intro M
  have hd : 0 < 4 * c / 9 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt ((M - 10 / 9) / (4 * c / 9))
  have h := (div_lt_iff₀ hd).mp hk
  have hlower := collisionEnergy_linear hf (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hlower
  exact ⟨k + 1, by omega, by nlinarith⟩

end SyracuseReport
