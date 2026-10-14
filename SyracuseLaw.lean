import Projection
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! The actual finite Syracuse probability laws, projective consistency,
normalized densities, geometric atom weights and one-step lower bounds.
The geometric letters are auxiliary independent samples, not assumptions
about valuations along deterministic Collatz trajectories.
-/

namespace SyracuseReport

noncomputable def letterLaw : PMF ℕ+ :=
  (ProbabilityTheory.geometricPMF (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).map
    (fun a : ℕ => ⟨a + 1, Nat.succ_pos a⟩)

noncomputable def affineStep (n : ℕ) (a : ℕ+) (z : ZMod (3 ^ n)) :
    ZMod (3 ^ (n + 1)) :=
  ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * (3 * z.val + 1)

noncomputable def syracuseLaw : (n : ℕ) → PMF (ZMod (3 ^ n))
  | 0 => PMF.pure 0
  | n + 1 => letterLaw.bind (fun a => (syracuseLaw n).map (affineStep n a))

noncomputable def density (n : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  (2 / 3 : ℝ) * (3 : ℝ) ^ n * (syracuseLaw n r).toReal

theorem affineStep_scaled (n : ℕ) (a : ℕ+) (z : ZMod (3 ^ n)) :
    (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * affineStep n a z = 3 * z.val + 1 := by
  unfold affineStep
  rw [← mul_assoc, two_power_mul_inv, one_mul]

theorem affineStep_project {q t : ℕ} (h : t ≤ q) (a : ℕ+) (z : ZMod (3 ^ q)) :
    residueProjection (Nat.add_le_add_right h 1) (affineStep q a z) =
      affineStep t a (residueProjection h z) := by
  let P := residueProjection (Nat.add_le_add_right h 1)
  let y := residueProjection h z
  have hs : (3 : ZMod (3 ^ (t + 1))) * (z.val : ℤ) =
      (3 : ZMod (3 ^ (t + 1))) * (y.val : ℤ) := by
    have hz : (z.val : ZMod (3 ^ t)) = (y.val : ZMod (3 ^ t)) := by
      simp only [ZMod.natCast_zmod_val]
      simpa only [Int.cast_natCast] using (residueProjection_val h z).symm
    have H := (scaled_int_cast_eq_iff 1 t z.val y.val).mpr (by exact_mod_cast hz)
    rw [Nat.add_comm 1 t] at H
    simpa only [pow_one] using H
  have hi := two_power_mul_inv (t + 1) (a : ℕ)
  have hp2 : P 2 = 2 := map_ofNat P 2
  have hp3 : P 3 = 3 := map_ofNat P 3
  have hpz : P (z.val : ZMod (3 ^ (q + 1))) = (z.val : ZMod (3 ^ (t + 1))) := map_natCast P z.val
  have hp : (2 : ZMod (3 ^ (t + 1))) ^ (a : ℕ) * P (affineStep q a z) =
      (2 : ZMod (3 ^ (t + 1))) ^ (a : ℕ) * affineStep t a y := by
    calc
      _ = P ((2 : ZMod (3 ^ (q + 1))) ^ (a : ℕ) * affineStep q a z) := by simp only [map_mul, map_pow, hp2]
      _ = 3 * (z.val : ZMod (3 ^ (t + 1))) + 1 := by rw [affineStep_scaled]; simp only [map_add, map_mul, hp3, hpz, map_one]
      _ = 3 * (y.val : ZMod (3 ^ (t + 1))) + 1 := by simpa only [Int.cast_natCast] using congrArg (fun v => v + 1) hs
      _ = _ := (affineStep_scaled t a y).symm
  have hcancel := congrArg (fun v => ((2 : ZMod (3 ^ (t + 1))) ^ (a : ℕ))⁻¹ * v) hp
  have hi' : ((2 : ZMod (3 ^ (t + 1))) ^ (a : ℕ))⁻¹ * (2 : ZMod (3 ^ (t + 1))) ^ (a : ℕ) = 1 := by
    rw [mul_comm]; exact hi
  simpa only [← mul_assoc, hi', one_mul] using hcancel

theorem syracuseLaw_project {q t : ℕ} (h : t ≤ q) :
    (syracuseLaw q).map (residueProjection h) = syracuseLaw t := by
  induction t generalizing q with
  | zero =>
    have hf : (residueProjection h : ZMod (3 ^ q) → ZMod (3 ^ 0)) =
        Function.const _ 0 := by
      funext z
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    rw [hf, PMF.map_const]
    rfl
  | succ t ih =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hqt : t ≤ q := by omega
    simp only [syracuseLaw, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind letterLaw)
    funext a
    have hf : (residueProjection h) ∘ affineStep q a =
        (affineStep t a) ∘ residueProjection hqt := by
      funext z
      exact affineStep_project hqt a z
    rw [hf, ← PMF.map_comp, ih hqt]

open scoped BigOperators ENNReal

/-- The exact sum of fine atoms above a coarse residue. -/
theorem syracuseLaw_project_atoms {q t : ℕ} (h : t ≤ q) (r : ZMod (3 ^ t)) :
    syracuseLaw t r = ∑ z : ZMod (3 ^ q),
      if residueProjection h z = r then syracuseLaw q z else 0 := by
  classical
  rw [← syracuseLaw_project h, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hh : residueProjection h z = r
  · simp [hh]
  · simp [hh, Ne.symm hh]

/-- Real-valued version, with finiteness of all atom masses justified. -/
theorem syracuseLaw_project_real {q t : ℕ} (h : t ≤ q) (r : ZMod (3 ^ t)) :
    (syracuseLaw t r).toReal = ∑ z : ZMod (3 ^ q),
      if residueProjection h z = r then (syracuseLaw q z).toReal else 0 := by
  classical
  rw [syracuseLaw_project_atoms h r, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> rfl
  · intro z hz
    split_ifs
    · exact (syracuseLaw q).apply_ne_top z
    · exact ENNReal.zero_ne_top

theorem syracuseLaw_real_sum (n : ℕ) :
    (∑ r : ZMod (3 ^ n), (syracuseLaw n r).toReal) = 1 := by
  have hs : (∑ r : ZMod (3 ^ n), syracuseLaw n r) = 1 := by
    simpa only [tsum_fintype] using (syracuseLaw n).tsum_coe
  have hr := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_sum (fun r _ => (syracuseLaw n).apply_ne_top r),
    ENNReal.toReal_one] at hr
  exact hr

theorem density_nonneg (n : ℕ) (r : ZMod (3 ^ n)) : 0 ≤ density n r := by
  unfold density
  positivity

theorem finiteMean_density (n : ℕ) : finiteMean (density n) = 2 / 3 := by
  unfold finiteMean density
  rw [← Finset.mul_sum, syracuseLaw_real_sum, mul_one, ZMod.card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hn : (3 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- Density projectivity, including the change in normalization. -/
theorem density_project {q t : ℕ} (h : t ≤ q) (r : ZMod (3 ^ t)) :
    density t r = ((3 : ℝ) ^ t / (3 : ℝ) ^ q) *
      ∑ z : ZMod (3 ^ q), if residueProjection h z = r then density q z else 0 := by
  classical
  unfold density
  rw [syracuseLaw_project_real h r]
  have hs : (∑ z : ZMod (3 ^ q), if residueProjection h z = r then
      (2 / 3 : ℝ) * (3 : ℝ) ^ q * (syracuseLaw q z).toReal else 0) =
      (2 / 3 : ℝ) * (3 : ℝ) ^ q * ∑ z : ZMod (3 ^ q),
      if residueProjection h z = r then (syracuseLaw q z).toReal else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> ring
  rw [hs]
  have hq : (3 : ℝ) ^ q ≠ 0 := by positivity
  field_simp

/-- The geometric letter distribution is exactly the one in the paper. -/
theorem letterLaw_succ (n : ℕ) :
    letterLaw ⟨n + 1, Nat.succ_pos n⟩ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  classical
  have hm := PMF.map_apply (fun a : ℕ => (⟨a + 1, Nat.succ_pos a⟩ : ℕ+))
    (ProbabilityTheory.geometricPMF (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
  change letterLaw ⟨n + 1, Nat.succ_pos n⟩ = _ at hm
  rw [hm]
  simp only [Subtype.mk.injEq, Nat.add_right_cancel_iff]
  rw [tsum_eq_single n]
  · simp only [ite_true]
    change ENNReal.ofReal ((1 - (1 / 2 : ℝ)) ^ n * (1 / 2)) = _
    congr 1
    norm_num [pow_succ]
  · intro b hb
    simp [Ne.symm hb]

theorem letterLaw_real (a : ℕ+) :
    (letterLaw a).toReal = 1 / (2 : ℝ) ^ (a : ℕ) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt a.pos)
  have ha : a = ⟨n + 1, Nat.succ_pos n⟩ := Subtype.ext hn
  rw [ha, letterLaw_succ, ENNReal.toReal_ofReal (by positivity)]
  simp only [one_div_pow]
  rfl

/-- A single nonnegative term in the exact law recursion. -/
theorem syracuseLaw_one_step (n : ℕ) (a : ℕ+) (z : ZMod (3 ^ n))
    (r : ZMod (3 ^ (n + 1))) (h : affineStep n a z = r) :
    letterLaw a * syracuseLaw n z ≤ syracuseLaw (n + 1) r := by
  classical
  have hz : syracuseLaw n z ≤ ((syracuseLaw n).map (affineStep n a)) r := by
    rw [PMF.map_apply]
    have hh := ENNReal.le_tsum (f := fun x => if r = affineStep n a x then syracuseLaw n x else 0) z
    convert hh using 1
    · simp [h]
    · apply tsum_congr
      intro x
      split_ifs <;> rfl
  have ha : letterLaw a * ((syracuseLaw n).map (affineStep n a)) r ≤
      syracuseLaw (n + 1) r := by
    change _ ≤ ∑' b : ℕ+, letterLaw b * ((syracuseLaw n).map (affineStep n b)) r
    exact ENNReal.le_tsum (f := fun b : ℕ+ =>
      letterLaw b * ((syracuseLaw n).map (affineStep n b)) r) a
  exact (mul_le_mul' le_rfl hz).trans ha

/-- The normalized one-step lower bound with the exact geometric weight. -/
theorem density_one_step (n : ℕ) (a : ℕ+) (z : ZMod (3 ^ n))
    (r : ZMod (3 ^ (n + 1))) (h : affineStep n a z = r) :
    (3 / (2 : ℝ) ^ (a : ℕ)) * density n z ≤ density (n + 1) r := by
  have hm := ENNReal.toReal_mono ((syracuseLaw (n + 1)).apply_ne_top r)
    (syracuseLaw_one_step n a z r h)
  rw [ENNReal.toReal_mul, letterLaw_real] at hm
  have hp : 0 ≤ (2 / 3 : ℝ) * (3 : ℝ) ^ (n + 1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hp
  unfold density
  convert hh using 1
  rw [pow_succ]
  ring

end SyracuseReport
