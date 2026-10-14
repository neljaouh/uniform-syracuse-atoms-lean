import DensityGeometry

/-! A countable set meeting every unit cylinder, with a strictly smaller
upper local exponent. The points and cylinder probabilities are explicit. -/
namespace SyracuseReport
open Filter
open scoped Topology

noncomputable def padicTwoUnit : (PadicInt 3)ˣ :=
  (PadicInt.isUnit_iff.mpr ((PadicInt.norm_natCast_eq_one_iff (p := 3) (n := 2)).mpr
    (by decide : Nat.Coprime 3 2))).unit

theorem padicTwoUnit_val : (padicTwoUnit : PadicInt 3) = 2 := IsUnit.unit_spec _

noncomputable def spikePoint (a : ℕ+) : PadicInt 3 :=
  ((padicTwoUnit⁻¹ : (PadicInt 3)ˣ) : PadicInt 3) ^ (a : ℕ) * (-2)

theorem spikePoint_scaled (a : ℕ+) :
    (2 : PadicInt 3) ^ (a : ℕ) * spikePoint a = -2 := by
  change (2 : PadicInt 3) ^ (a : ℕ) *
    (((padicTwoUnit⁻¹ : (PadicInt 3)ˣ) : PadicInt 3) ^ (a : ℕ) * (-2)) = -2
  rw [← padicTwoUnit_val, ← mul_assoc, ← mul_pow]
  simp

theorem spikePoint_reduction (n : ℕ) (a : ℕ+) :
    PadicInt.toZModPow (n + 1) (spikePoint a) = affineStep n a (-1) := by
  have hs := congrArg (PadicInt.toZModPow (n + 1)) (spikePoint_scaled a)
  simp only [map_mul, map_pow, map_ofNat, map_neg] at hs
  have hf : (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * affineStep n a (-1) = -2 := by
    have hform := affineStep_intCast n a (-1)
    simp only [Int.cast_neg, Int.cast_one] at hform
    rw [hform]
    rw [← mul_assoc, two_power_mul_inv, one_mul]
    ring
  have hi : ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * 2 ^ (a : ℕ) = 1 := by
    rw [mul_comm]
    exact two_power_mul_inv (n + 1) (a : ℕ)
  have hh := congrArg (fun z => ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * z)
    (hs.trans hf.symm)
  simpa only [← mul_assoc, hi, one_mul] using hh

theorem spike_density_lower (a : ℕ+) (n : ℕ) :
    (2 / (2 : ℝ) ^ (a : ℕ)) * (3 / 2 : ℝ) ^ n ≤
      density (n + 1) (PadicInt.toZModPow (n + 1) (spikePoint a)) := by
  rw [spikePoint_reduction]
  have hs := density_one_step n a (-1) (affineStep n a (-1)) rfl
  have hb := mul_le_mul_of_nonneg_left (neg_one_density_lower n)
    (show (0 : ℝ) ≤ 3 / (2 : ℝ) ^ (a : ℕ) by positivity)
  have he : (3 / (2 : ℝ) ^ (a : ℕ)) * ((2 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) =
      (2 / (2 : ℝ) ^ (a : ℕ)) * (3 / 2 : ℝ) ^ n := by ring
  rw [he] at hb
  exact hb.trans hs

theorem spike_atom_lower (a : ℕ+) (n : ℕ) :
    1 / (2 : ℝ) ^ ((a : ℕ) + n) ≤
      atomMass (n + 1) (PadicInt.toZModPow (n + 1) (spikePoint a)) := by
  have h := spike_density_lower a n
  change _ ≤ (2 / 3 : ℝ) * (3 : ℝ) ^ (n + 1) *
    atomMass (n + 1) (PadicInt.toZModPow (n + 1) (spikePoint a)) at h
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < (2 / 3 : ℝ) * 3 ^ (n + 1) by positivity)
  convert h using 1
  rw [pow_succ, pow_add, div_pow]
  field_simp
  <;> ring

theorem spike_point_in_unitRegion (a : ℕ+) : spikePoint a ∈ unitRegion := by
  have hd := spike_density_lower a 0
  have hpos : 0 < density 1 (PadicInt.toZModPow 1 (spikePoint a)) := by
    norm_num only [pow_zero, mul_one] at hd
    exact (by positivity : (0 : ℝ) < 2 / (2 : ℝ) ^ (a : ℕ)).trans_le hd
  have hu : IsUnit (PadicInt.toZModPow 1 (spikePoint a)) := by
    by_contra h
    rw [density_nonunit (by norm_num : 1 ≤ 1) _ h] at hpos
    linarith
  rw [unitRegion_eq_unit_reduction]
  exact hu

theorem spike_dimension_upper (a : ℕ+) (n : ℕ) :
    localDimensionRatio (spikePoint a) n ≤
      (((a : ℕ) + n : ℕ) : ℝ) * Real.log 2 /
        ((((n + 1 : ℕ) : ℝ)) * Real.log 3) := by
  have hlo := spike_atom_lower a n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ ((a : ℕ) + n)) hlo
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow,
    zero_sub] at hlog
  unfold localDimensionRatio
  apply div_le_div_of_nonneg_right _
    (by positivity : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) * Real.log 3)
  linarith

theorem spike_dimension_eventually (a : ℕ+) (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      localDimensionRatio (spikePoint a) n ≤ Real.log 2 / Real.log 3 + epsilon := by
  have hl3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hnplus : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hn : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * Real.log 3) atTop atTop := by
    simpa only [mul_comm] using hnplus.const_mul_atTop hl3
  have hconst : Tendsto (fun _ : ℕ => (((a : ℕ) : ℝ) - 1) * Real.log 2)
      atTop (𝓝 ((((a : ℕ) : ℝ) - 1) * Real.log 2)) := tendsto_const_nhds
  have hratio := hconst.div_atTop hn
  have hlim : Tendsto (fun n : ℕ => (((a : ℕ) + n : ℕ) : ℝ) * Real.log 2 /
      ((((n + 1 : ℕ) : ℝ)) * Real.log 3)) atTop (𝓝 (Real.log 2 / Real.log 3)) := by
    have hs : Tendsto (fun n : ℕ => Real.log 2 / Real.log 3 +
        ((((a : ℕ) : ℝ) - 1) * Real.log 2) / ((((n + 1 : ℕ) : ℝ)) * Real.log 3))
        atTop (𝓝 (Real.log 2 / Real.log 3)) := by
      simpa only [add_zero] using
        (show Tendsto (fun _ : ℕ => Real.log 2 / Real.log 3) atTop
          (𝓝 (Real.log 2 / Real.log 3)) from tendsto_const_nhds).add hratio
    convert hs using 1
    funext n
    push_cast
    field_simp [hl3.ne', show (n : ℝ) + 1 ≠ 0 by positivity]
    <;> ring
  have hev := hlim.eventually (eventually_lt_nhds (by linarith :
    Real.log 2 / Real.log 3 < Real.log 2 / Real.log 3 + epsilon))
  filter_upwards [hev] with n hn
  exact (spike_dimension_upper a n).trans hn.le

def DenseSpikeGeometryStatement : Prop :=
  ∃ S : Set (PadicInt 3), S.Countable ∧ S ⊆ unitRegion ∧
    (∀ q : ℕ, 1 ≤ q → ∀ r : ZMod (3 ^ q), IsUnit r →
      ∃ x, x ∈ S ∧ x ∈ cylinder q r) ∧
    ∀ x ∈ S, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        localDimensionRatio x n ≤ Real.log 2 / Real.log 3 + epsilon

theorem dense_spike_geometry : DenseSpikeGeometryStatement := by
  refine ⟨Set.range spikePoint, Set.countable_range _, ?_, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact spike_point_in_unitRegion a
  · intro q hq r hr
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    obtain ⟨a, ha⟩ := exists_affine_neg_one k r hr
    refine ⟨spikePoint a, ⟨a, rfl⟩, ?_⟩
    change PadicInt.toZModPow (k + 1) (spikePoint a) = r
    rw [spikePoint_reduction, ha]
  · rintro x ⟨a, rfl⟩ epsilon he
    exact spike_dimension_eventually a epsilon he

end SyracuseReport
