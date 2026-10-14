import BoundedInverse
import Cylinder
import MinimumLimit

namespace SyracuseReport
open scoped BigOperators Topology

theorem uniform_density_of_positive_cylinder {q : ℕ} {y : ZMod (3 ^ q)}
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcyl : ∀ h, (hqh : q ≤ h) → ∀ x : ZMod (3 ^ h),
      residueProjection hqh x = y → kappa ≤ density h x) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → d ≤ density n r := by
  let V := 2 * 3 ^ q
  let d := 3 / (2 : ℝ) ^ V * kappa
  have hd : 0 < d := by dsimp [d]; positivity
  have hlarge : ∀ n : ℕ, q + 1 ≤ n → ∀ r : ZMod (3 ^ n), IsUnit r →
      d ≤ density n r := by
    intro n hn r hr
    obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hqh : q ≤ h := by omega
    obtain ⟨v, z, hv, hz, hstep⟩ := bounded_inverse_into_cylinder q h hqh y r hr
    have hzfloor := hcyl h hqh z hz
    have hp : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (v : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hv
    have hs := density_one_step h v z r hstep
    apply le_trans _ hs
    dsimp [d, V]
    calc
      3 / (2 : ℝ) ^ (2 * 3 ^ q) * kappa =
          3 * (1 / 2 : ℝ) ^ (2 * 3 ^ q) * kappa := by rw [one_div_pow]; ring
      _ ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * kappa := by gcongr
      _ ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * density h z := by gcongr
      _ = 3 / (2 : ℝ) ^ (v : ℕ) * density h z := by
        rw [one_div_pow]
        ring
  refine ⟨d, hd, ?_⟩
  intro n hn r hr
  by_cases hbig : q + 1 ≤ n
  · exact hlarge n hbig r hr
  · have hle : n ≤ q + 1 := by omega
    have hsum : (∑ z : ZMod (3 ^ (q + 1)),
        if residueProjection hle z = r then d else 0) ≤
      ∑ z : ZMod (3 ^ (q + 1)),
        if residueProjection hle z = r then density (q + 1) z else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · apply hlarge (q + 1) le_rfl z
        exact (residueProjection_isUnit_iff hle hn z).mp (hz ▸ hr)
      · exact le_rfl
    rw [projection_fiber_constant, projection_fiber_density] at hsum
    exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < 3 ^ (q + 1 - n))

theorem coreWitness_uniform_density (W : CoreWitness) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → d ≤ density n r := by
  obtain ⟨q, y, kappa, _, _, hkappa, hcyl⟩ := W.positive_cylinder
  exact uniform_density_of_positive_cylinder hkappa hcyl

/-- The cylinder criterion yields the uniform atom floor. -/
theorem atomFloor_of_coreWitness (W : CoreWitness) : AtomFloorStatement := by
  obtain ⟨d, hd, hfloor⟩ := coreWitness_uniform_density W
  refine ⟨(3 / 2 : ℝ) * d, by positivity, ?_⟩
  intro n hn r hr
  apply atom_bound_of_density n (syracuseLaw n r).toReal d
  have hf := hfloor n hn r hr
  unfold density at hf
  exact hf

theorem mainTheoremA_of_coreWitness (W : CoreWitness) : MainTheoremA := by
  have hfloor := atomFloor_of_coreWitness W
  obtain ⟨c, hc, hF⟩ := hfloor
  obtain ⟨ell, hell, hupper, hlim, hratio, hexponent⟩ :=
    minimum_asymptotics.2.2 c hc hF
  exact ⟨⟨c, hc, hF⟩, minimum_asymptotics.1,
    ell, hell, hupper, hlim, hratio, hexponent⟩

end SyracuseReport
