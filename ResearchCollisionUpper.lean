import ResearchFibrePartition
import DensityEnergy

/-! Quadratic upper collision energy for the actual finite Syracuse law.
The constant consists of convergent one-letter moments. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def collisionWordCost (w : Word) : ℝ :=
  tiltedWordWeight w * (w.total : ℝ) ^ 2 * (1 + normalizedWordOffset w)

theorem collisionWordCost_nonneg (w : Word) : 0 ≤ collisionWordCost w := by
  unfold collisionWordCost
  have := (tiltedWordWeight_pos w).le
  have := normalizedWordOffset_nonneg w
  positivity

theorem collisionWordCost_hasSum (n : ℕ) :
    HasSum (fun w : {w : Word // w.length = n} => collisionWordCost w.1)
      (tiltedTotalSecondMomentFormula n + tiltedOffsetSecondMomentFormula n) := by
  have h := (hasSum_fixedLength_tilted_total_sq n).add
    (hasSum_fixedLength_tilted_total_sq_offset n)
  apply h.congr_fun
  intro w
  dsimp [collisionWordCost]
  ring

/-- The scaling converts geometric squared probabilities to the normalized
tilted word law. -/
theorem scaled_fibre_cost_le (n A : ℕ) (hA : 1 ≤ A) (R : ℤ) :
    (3 : ℝ) ^ n * ((A : ℝ) * ((A : ℝ) + 1) *
      ((2 * ∑ w ∈ fixedTotalContributors n A R,
        (1 + (w.numerator : ℝ) / (3 : ℝ) ^ n)) / ((2 : ℝ) ^ A) ^ 2)) ≤
      4 * ∑ w ∈ fixedTotalContributors n A R, collisionWordCost w := by
  classical
  have hAn : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hpoly : 2 * (A : ℝ) * ((A : ℝ) + 1) ≤ 4 * (A : ℝ) ^ 2 := by
    nlinarith
  calc
    _ = ∑ w ∈ fixedTotalContributors n A R,
        (2 * (A : ℝ) * ((A : ℝ) + 1)) *
          (tiltedWordWeight w * (1 + normalizedWordOffset w)) := by
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hlen, htotal, _⟩ := (mem_fixedTotalContributors_iff n A R w).mp hw
      rw [tiltedWordWeight_probability_sq]
      simp only [Word.probability, normalizedWordOffset, hlen, htotal]
      ring
    _ ≤ ∑ w ∈ fixedTotalContributors n A R, 4 * collisionWordCost w := by
      apply Finset.sum_le_sum
      intro w hw
      have htotal := ((mem_fixedTotalContributors_iff n A R w).mp hw).2.1
      have hn := (tiltedWordWeight_pos w).le
      have hy := normalizedWordOffset_nonneg w
      have h := mul_le_mul_of_nonneg_right hpoly
        (show 0 ≤ tiltedWordWeight w * (1 + normalizedWordOffset w) by positivity)
      convert h using 1 <;> dsimp [collisionWordCost] <;> rw [htotal] <;> ring
    _ = _ := by rw [Finset.mul_sum]

theorem finite_scaled_atom_cost_bound (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (R : ℤ) :
    (3 : ℝ) ^ n * (∑ A ∈ Finset.Ico n N,
      ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A) ^ 2 ≤
      (4 / (n : ℝ)) * ∑ A ∈ Finset.Ico n N,
        ∑ w ∈ fixedTotalContributors n A R, collisionWordCost w := by
  have h := mul_le_mul_of_nonneg_left (finite_atom_fibre_cost_bound n N hn hN R)
    (show 0 ≤ (3 : ℝ) ^ n by positivity)
  calc
    _ ≤ _ := h
    _ = (1 / (n : ℝ)) * ∑ A ∈ Finset.Ico n N,
        (3 : ℝ) ^ n * ((A : ℝ) * ((A : ℝ) + 1) *
          ((2 * ∑ w ∈ fixedTotalContributors n A R,
            (1 + (w.numerator : ℝ) / (3 : ℝ) ^ n)) / ((2 : ℝ) ^ A) ^ 2)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (1 / (n : ℝ)) * ∑ A ∈ Finset.Ico n N,
        4 * ∑ w ∈ fixedTotalContributors n A R, collisionWordCost w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro A hA
      exact scaled_fibre_cost_le n A (hn.trans (Finset.mem_Ico.mp hA).1) R
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A uniform bound for every finite valuation truncation, with all
residues included. -/
theorem finite_collision_energy_cost_bound (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    (3 : ℝ) ^ n * ∑ r : ZMod (3 ^ n),
      (∑ A ∈ Finset.Ico n N,
        ((fixedTotalContributors n A (r.val : ℤ)).card : ℝ) / (2 : ℝ) ^ A) ^ 2 ≤
      (4 / (n : ℝ)) *
        (tiltedTotalSecondMomentFormula n + tiltedOffsetSecondMomentFormula n) := by
  classical
  calc
    _ = ∑ r : ZMod (3 ^ n), (3 : ℝ) ^ n *
        (∑ A ∈ Finset.Ico n N,
          ((fixedTotalContributors n A (r.val : ℤ)).card : ℝ) / (2 : ℝ) ^ A) ^ 2 :=
      Finset.mul_sum ..
    _ ≤ ∑ r : ZMod (3 ^ n), (4 / (n : ℝ)) * ∑ A ∈ Finset.Ico n N,
        ∑ w ∈ fixedTotalContributors n A (r.val : ℤ), collisionWordCost w := by
      apply Finset.sum_le_sum
      intro r _
      exact finite_scaled_atom_cost_bound n N hn hN (r.val : ℤ)
    _ = (4 / (n : ℝ)) * ∑ r : ZMod (3 ^ n), ∑ A ∈ Finset.Ico n N,
        ∑ w ∈ fixedTotalContributors n A (r.val : ℤ), collisionWordCost w :=
      (Finset.mul_sum ..).symm
    _ ≤ (4 / (n : ℝ)) * ∑' w : {w : Word // w.length = n}, collisionWordCost w.1 :=
      mul_le_mul_of_nonneg_left
        (finite_fibre_weight_sum_le n N collisionWordCost collisionWordCost_nonneg
          (collisionWordCost_hasSum n).summable) (by positivity)
    _ = _ := by rw [(collisionWordCost_hasSum n).tsum_eq]


theorem word_length_le_total (w : Word) : w.length ≤ w.total := by
  induction w with
  | nil => rfl
  | snoc w a ih =>
      have ha := a.pos
      simp only [Word.length, Word.total]
      omega

theorem fixedTotalContributors_empty_of_lt (n A : ℕ) (hA : A < n) (R : ℤ) :
    fixedTotalContributors n A R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hlen, htotal, _⟩ := (mem_fixedTotalContributors_iff n A R w).mp hw
  have h := word_length_le_total w
  omega

/-- Finite valuation cutoffs exhaust the actual Syracuse atom. -/
theorem tendsto_truncated_syracuse_atom (n : ℕ) (R : ℤ) :
    Filter.Tendsto (fun N : ℕ => ∑ A ∈ Finset.Ico n N,
      ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A)
      Filter.atTop (nhds (syracuseLaw n (R : ZMod (3 ^ n))).toReal) := by
  classical
  let u : ℕ → ℝ := fun A =>
    ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A
  have hz : ∑ A ∈ Finset.range n, u A = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    simp [u, fixedTotalContributors_empty_of_lt n A (Finset.mem_range.mp hA) R]
  have heq : ∀ᶠ N : ℕ in Filter.atTop,
      (∑ A ∈ Finset.range N, u A) = ∑ A ∈ Finset.Ico n N, u A := by
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    have h := Finset.sum_range_add_sum_Ico u hN
    rw [hz, zero_add] at h
    exact h.symm
  exact (finite_syracuse_atom_total_series n R).tendsto_sum_nat.congr' heq

/-- An unconditional bound for the full collision sum of the actual law. -/
theorem actual_collision_moment_bound (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℝ) ^ n * ∑ r : ZMod (3 ^ n), (atomMass n r) ^ 2 ≤
      (4 / (n : ℝ)) *
        (tiltedTotalSecondMomentFormula n + tiltedOffsetSecondMomentFormula n) := by
  classical
  have hlim := Filter.Tendsto.const_mul ((3 : ℝ) ^ n)
    (tendsto_finset_sum Finset.univ (fun (r : ZMod (3 ^ n)) _ =>
      (tendsto_truncated_syracuse_atom n (r.val : ℤ)).pow 2))
  have hlim' : Filter.Tendsto (fun N : ℕ =>
      (3 : ℝ) ^ n * ∑ r : ZMod (3 ^ n),
        (∑ A ∈ Finset.Ico n N,
          ((fixedTotalContributors n A (r.val : ℤ)).card : ℝ) / (2 : ℝ) ^ A) ^ 2)
      Filter.atTop (nhds ((3 : ℝ) ^ n * ∑ r : ZMod (3 ^ n), (atomMass n r) ^ 2)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, atomMass] using hlim
  apply le_of_tendsto hlim'
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  exact finite_collision_energy_cost_bound n N hn hN

noncomputable def quadraticCollisionConstant : ℝ :=
  4 * (tiltedSecondMoment + tiltedFirstMoment ^ 2 + tiltedOffsetCubicConstant)

/-- The all-depth polynomial upper bound needed for subcritical density
moments. Its constant is independent of the depth. -/
theorem actual_collision_quadratic_bound (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℝ) ^ n * ∑ r : ZMod (3 ^ n), (atomMass n r) ^ 2 ≤
      quadraticCollisionConstant * (n : ℝ) ^ 2 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let c := tiltedSecondMoment + tiltedFirstMoment ^ 2
  have hc : 0 ≤ c := add_nonneg tiltedSecondMoment_nonneg (sq_nonneg _)
  have hQ := tiltedTotalSecondMomentFormula_le n
  have hW := tiltedOffsetSecondMomentFormula_le_cubic_bound n
  have hnc : (n : ℝ) ^ 2 * c ≤ (n : ℝ) ^ 3 * c := by
    have := mul_nonneg hc (mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn1))
    nlinarith
  calc
    _ ≤ _ := actual_collision_moment_bound n hn
    _ ≤ (4 / (n : ℝ)) * ((n : ℝ) ^ 3 * c + tiltedOffsetCubicConstant * (n : ℝ) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [c] at hnc
      linarith
    _ = _ := by
      dsimp [quadraticCollisionConstant, c]
      field_simp
      <;> ring

end SyracuseReport
