import PaperStatements

/-! Stabilization preserves a positive cylinder for the selected
approximants themselves, before any comparison with the full law. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem CoreWitness.positive_approximant_cylinder (W : CoreWitness) :
    ∃ (N0 q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ N0 ∧ q = W.depth N0 ∧ 1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ N : ℕ, N0 ≤ N → (hqN : q ≤ W.depth N) →
        ∀ r : ZMod (3 ^ W.depth N), residueProjection hqN r = y →
          kappa ≤ W.approximate N r := by
  have hevent : ∀ᶠ N : ℕ in atTop, W.variation N < W.mark / 2 :=
    (tendsto_order.mp W.variation_tendsto).2 _ (by linarith [W.mark_positive])
  obtain ⟨K, hK⟩ := eventually_atTop.mp hevent
  let N0 := max K 1
  have hN0 : 1 ≤ N0 := le_max_right _ _
  have hvar : W.variation N0 < W.mark / 2 := hK N0 (le_max_left _ _)
  obtain ⟨y, hy, hmark⟩ := W.positive_mark N0 hN0
  refine ⟨N0, W.depth N0, y, W.mark / 2, hN0, rfl,
    W.depth_positive N0 hN0, hy, by linarith [W.mark_positive], ?_⟩
  intro N hN hqN r hr
  have hstab := W.stabilization N0 N hN0 hN hqN r
  rw [hr] at hstab
  have hlower := (abs_le.mp hstab).1
  linarith

end SyracuseReport
