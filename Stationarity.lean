import SyracuseLimit

/-! The stationary cylinder equations determine the finite laws recursively.
Existence of the limiting probability and the Borel cylinder uniqueness
theorem therefore give existence and uniqueness of the stationary law.
-/
namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem cylinder_zero (r : ZMod (3 ^ 0)) : cylinder 0 r = Set.univ := by
  ext x
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  change (_ : ZMod 1) = _
  exact Subsingleton.elim _ _

theorem syracuseLaw_recursion (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    syracuseLaw (n + 1) r =
      ∑' a : ℕ+, letterLaw a * ∑ z : ZMod (3 ^ n),
        if affineStep n a z = r then syracuseLaw n z else 0 := by
  classical
  simp only [syracuseLaw, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  apply tsum_congr
  intro a
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : r = affineStep n a z
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem syracuseLimit_stationary (μ : Measure (PadicInt 3))
    (hμ : IsSyracuseLimit μ) : IsSyracuseStationary μ := by
  refine ⟨hμ.1, ?_⟩
  intro n r
  simp_rw [hμ.2]
  exact syracuseLaw_recursion n r

theorem stationary_isSyracuseLimit (ρ : Measure (PadicInt 3))
    (hρ : IsSyracuseStationary ρ) : IsSyracuseLimit ρ := by
  classical
  letI := hρ.1
  refine ⟨hρ.1, ?_⟩
  intro n
  induction n with
  | zero =>
    intro r
    rw [cylinder_zero, measure_univ]
    have hr : r = 0 := by
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    subst r
    exact (PMF.pure_apply_self (0 : ZMod (3 ^ 0))).symm
  | succ n ih =>
    intro r
    rw [hρ.2 n r]
    simp_rw [ih]
    exact (syracuseLaw_recursion n r).symm

theorem paper_lem_stationary : PaperStatements.lem_stationary := by
  obtain ⟨μ, hμ⟩ := exists_syracuseLimit
  refine ⟨μ, hμ, syracuseLimit_stationary μ hμ, ?_⟩
  intro ρ hρ
  exact syracuseLimit_unique ρ μ (stationary_isSyracuseLimit ρ hρ) hμ

end SyracuseReport
