import SelectedDensityIncrement
set_option backward.isDefEq.respectTransparency false

/-! Terminal depths can vary continuously between successive block scales.
This estimate is needed when selecting word lengths for a prescribed cutoff. -/
namespace SyracuseReport
open scoped BigOperators

noncomputable def flexibleSelectedDensity (N t : ℕ) :
    ZMod (3 ^ (prefixDepth N + t)) → ℝ :=
  familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)

theorem flexibleSelectedDensity_comparison (C6 : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * C6 / (m : ℝ) ^ 6)
    (N t : ℕ) (hkt : terminalDepth N ≤ t) (ht : t ≤ 2 * blockLength N)
    (M : ℤ) :
    |flexibleSelectedDensity N t (M : ZMod (3 ^ (prefixDepth N + t))) -
      selectedDensity N (M : ZMod (3 ^ selectedDepth N))| ≤
      selectedKernelConstant N * ((2 / 3 : ℝ) * C6 / (terminalDepth N : ℝ) ^ 6) := by
  classical
  let f : ZMod (3 ^ t) → ℝ := fun r =>
    density t r - density (terminalDepth N) (residueProjection hkt r)
  have htpos : 1 ≤ t := (terminalDepth_pos N).trans hkt
  have heq : familyTransport (selectedPrefixes N) (prefixDepth N) t f
      (M : ZMod (3 ^ (prefixDepth N + t))) =
      flexibleSelectedDensity N t (M : ZMod (3 ^ (prefixDepth N + t))) -
        selectedDensity N (M : ZMod (3 ^ selectedDepth N)) := by
    rw [familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) t
      (fun _ hw => selectedPrefixes_length hw) f M, selectedDensity_integer_evaluation]
    change (∑ w ∈ selectedPrefixes N, wordTransport w t M f) =
      familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
        (M : ZMod (3 ^ (prefixDepth N + t))) - _
    rw [familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) t
      (fun _ hw => selectedPrefixes_length hw) (density t) M]
    dsimp [f]
    simp_rw [wordTransport_sub, wordTransport_lift]
    rw [Finset.sum_sub_distrib]
  have hnorm := paper_lem_kernel_bound N t htpos ht f
  change ‖familyTransport (selectedPrefixes N) (prefixDepth N) t f‖ ≤
    selectedKernelConstant N * finiteMean (fun r => |f r|) at hnorm
  have hm := hmix t (terminalDepth N) (terminalDepth_pos N) hkt
  have hK : 0 ≤ selectedKernelConstant N := by unfold selectedKernelConstant; positivity
  rw [← heq]
  exact (show |familyTransport (selectedPrefixes N) (prefixDepth N) t f
      (M : ZMod (3 ^ (prefixDepth N + t)))| ≤
      ‖familyTransport (selectedPrefixes N) (prefixDepth N) t f‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm
          (familyTransport (selectedPrefixes N) (prefixDepth N) t f)
          (M : ZMod (3 ^ (prefixDepth N + t)))).trans
    (hnorm.trans (mul_le_mul_of_nonneg_left hm hK))

end SyracuseReport
