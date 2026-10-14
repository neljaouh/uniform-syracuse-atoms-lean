import UnitProjection

/-! The finite least unit atom is attained. Projectivity over its three
unit lifts makes the normalized minimum antitone. -/

namespace SyracuseReport
open scoped BigOperators Topology
open Filter

theorem leastAtom_le (n : ℕ) (u : (ZMod (3 ^ (n + 1)))ˣ) :
    leastAtom n ≤ (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨u, rfl⟩

theorem le_leastAtom (n : ℕ) (a : ℝ)
    (h : ∀ u : (ZMod (3 ^ (n + 1)))ˣ,
      a ≤ (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal) :
    a ≤ leastAtom n := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  exact h u

theorem leastAtom_nonneg (n : ℕ) : 0 ≤ leastAtom n :=
  le_leastAtom n 0 (fun _ => ENNReal.toReal_nonneg)

theorem leastAtom_attained (n : ℕ) :
    ∃ u : (ZMod (3 ^ (n + 1)))ˣ,
      leastAtom n = (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal := by
  classical
  obtain ⟨u, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun u : (ZMod (3 ^ (n + 1)))ˣ =>
      (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal)
    Finset.univ_nonempty
  exact ⟨u, le_antisymm (leastAtom_le n u)
    (le_leastAtom n _ (fun v => hmin v (Finset.mem_univ v)))⟩

theorem leastAtom_le_of_isUnit (n : ℕ) (r : ZMod (3 ^ (n + 1))) (hr : IsUnit r) :
    leastAtom n ≤ (syracuseLaw (n + 1) r).toReal := by
  obtain ⟨u, rfl⟩ := hr
  exact leastAtom_le n u

theorem leastAtom_three_step (n : ℕ) : 3 * leastAtom (n + 1) ≤ leastAtom n := by
  classical
  obtain ⟨u, hu⟩ := leastAtom_attained n
  have hsum : (∑ z : ZMod (3 ^ (n + 2)),
      if residueProjection (by omega : n + 1 ≤ n + 2) z =
          (u : ZMod (3 ^ (n + 1))) then leastAtom (n + 1) else 0) ≤
    ∑ z : ZMod (3 ^ (n + 2)),
      if residueProjection (by omega : n + 1 ≤ n + 2) z =
          (u : ZMod (3 ^ (n + 1)))
      then (syracuseLaw (n + 2) z).toReal else 0 := by
    apply Finset.sum_le_sum
    intro z _
    split_ifs with hz
    · apply leastAtom_le_of_isUnit (n + 1) z
      apply (residueProjection_isUnit_iff
        (by omega : n + 1 ≤ n + 2) (by omega) z).mp
      rw [hz]
      exact u.isUnit
    · exact le_rfl
  rw [projection_fiber_constant] at hsum
  have hd : n + 2 - (n + 1) = 1 := by omega
  rw [hd, pow_one] at hsum
  rw [hu, syracuseLaw_project_real (by omega : n + 1 ≤ n + 2)]
  exact hsum

theorem normalizedMinimum_antitone : Antitone normalizedMinimum := by
  apply antitone_nat_of_succ_le
  intro n
  have h := mul_le_mul_of_nonneg_left (leastAtom_three_step n)
    (by positivity : (0 : ℝ) ≤ 3 ^ (n + 1))
  unfold normalizedMinimum
  rw [pow_succ]
  nlinarith [h]

end SyracuseReport
