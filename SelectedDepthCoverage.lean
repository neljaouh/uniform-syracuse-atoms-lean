import SelectedCoreWitness
import Mathlib.Data.Nat.Find
set_option backward.isDefEq.respectTransparency false

/-! Flexible terminal depths cover every sufficiently large word length. -/
namespace SyracuseReport
open Filter

theorem selectedDepth_interval (N0 h : ℕ) (hh : selectedDepth N0 ≤ h) :
    ∃ N : ℕ, N0 ≤ N ∧ selectedDepth N ≤ h ∧ h < selectedDepth (N + 1) := by
  have hex : ∃ k : ℕ, h < selectedDepth k := by
    obtain ⟨k, hk⟩ := eventually_atTop.1
      (selectedDepth_tendsto.eventually (eventually_gt_atTop h))
    exact ⟨k, hk k le_rfl⟩
  let k := Nat.find hex
  have hk : h < selectedDepth k := Nat.find_spec hex
  have hNk : N0 < k := by
    by_contra hc
    have hkn : k ≤ N0 := by omega
    exact (not_lt_of_ge ((selectedDepth_monotone hkn).trans hh)) hk
  let N := k - 1
  have hN : N0 ≤ N := by dsimp [N]; omega
  have hNk : N + 1 = k := by dsimp [N]; omega
  refine ⟨N, hN, ?_, by simpa only [hNk] using hk⟩
  apply le_of_not_gt
  exact Nat.find_min hex (by dsimp [N, k]; omega)

theorem exists_flexible_selected_depth (N0 h : ℕ) (hh : selectedDepth N0 ≤ h) :
    ∃ N t : ℕ, N0 ≤ N ∧ h = prefixDepth N + t ∧
      terminalDepth N ≤ t ∧ t ≤ blockLength N + terminalDepth (N + 1) := by
  obtain ⟨N, hN, hlo, hhi⟩ := selectedDepth_interval N0 h hh
  refine ⟨N, h - prefixDepth N, hN, ?_, ?_, ?_⟩
  · unfold selectedDepth at hlo
    omega
  · unfold selectedDepth at hlo
    omega
  · change h < (prefixDepth N + blockLength N) + terminalDepth (N + 1) at hhi
    omega

end SyracuseReport
