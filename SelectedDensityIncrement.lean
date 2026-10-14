import SelectedKernel
import SelectedTransportIdentities
import SelectedDensityBasics
set_option backward.isDefEq.respectTransparency false

/-! One-step uniform variation of the actual selected-prefix subdensities.
The integer form uses the same integer at every modulus, so no choice of a
lift or identification between unequal finite types enters the estimate. -/

namespace SyracuseReport
open scoped BigOperators

theorem finiteMean_subtract {X : Type*} [Fintype X] (f g : X → ℝ) :
    finiteMean (fun x => f x - g x) = finiteMean f - finiteMean g := by
  unfold finiteMean
  rw [Finset.sum_sub_distrib, sub_div]

theorem familyTransport_integer_evaluation (s : Finset Word) (d q : ℕ)
    (hlen : ∀ w ∈ s, w.length = d) (f : ZMod (3 ^ q) → ℝ) (M : ℤ) :
    familyTransport s d q f (M : ZMod (3 ^ (d + q))) =
      ∑ w ∈ s, wordTransport w q M f := by
  classical
  unfold familyTransport
  apply Finset.sum_congr rfl
  intro w hw
  apply wordTransport_congr_residue
  rw [hlen w hw]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem selectedDensity_integer_evaluation (N : ℕ) (M : ℤ) :
    selectedDensity N (M : ZMod (3 ^ selectedDepth N)) =
      ∑ w ∈ selectedPrefixes N, wordTransport w (terminalDepth N) M (density (terminalDepth N)) :=
  familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) (terminalDepth N)
    (fun _ hw => selectedPrefixes_length hw) (density (terminalDepth N)) M

theorem selected_block_rejected_mass (N : ℕ) :
    finiteMean (fun r : ZMod (3 ^ (blockLength N + terminalDepth (N + 1))) =>
      density (blockLength N + terminalDepth (N + 1)) r -
        familyTransport (selectedBlock N) (blockLength N) (terminalDepth (N + 1))
          (density (terminalDepth (N + 1))) r) =
        (2 / 3 : ℝ) * (1 - blockProbability N) := by
  rw [finiteMean_subtract, finiteMean_density, finiteMean_familyTransport
    (selectedBlock N) (blockLength N) (terminalDepth (N + 1))
    (fun _ hw => selectedBlock_length hw) (density (terminalDepth (N + 1))), finiteMean_density]
  unfold blockProbability
  ring

theorem selected_block_comparison_error (C6 : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * C6 / (m : ℝ) ^ 6)
    (N : ℕ) :
    finiteMean (fun r : ZMod (3 ^ (blockLength N + terminalDepth (N + 1))) =>
      |familyTransport (selectedBlock N) (blockLength N) (terminalDepth (N + 1))
          (density (terminalDepth (N + 1))) r -
        density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r)|) ≤
      (2 / 3 : ℝ) * (C6 / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N)) := by
  have h := block_error_bound
    (familyTransport (selectedBlock N) (blockLength N) (terminalDepth (N + 1))
      (density (terminalDepth (N + 1))))
    (density (blockLength N + terminalDepth (N + 1)))
    (fun r => density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r))
    ((2 / 3 : ℝ) * (1 - blockProbability N))
    ((2 / 3 : ℝ) * C6 / (terminalDepth N : ℝ) ^ 6)
    (fun r => familyTransport_density_le (selectedBlock N) (blockLength N)
      (terminalDepth (N + 1)) (fun _ hw => selectedBlock_length hw) r)
    (selected_block_rejected_mass N).le
    (hmix _ _ (terminalDepth_pos N) (nextBlockDepth_bounds N).1)
  convert h using 1
  ring

theorem selectedDensity_step_bound_integer (C6 : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * C6 / (m : ℝ) ^ 6)
    (N : ℕ) (M : ℤ) :
    |selectedDensity (N + 1) (M : ZMod (3 ^ selectedDepth (N + 1))) -
      selectedDensity N (M : ZMod (3 ^ selectedDepth N))| ≤ selectedIncrementBound C6 N := by
  classical
  let q := blockLength N + terminalDepth (N + 1)
  let h : ZMod (3 ^ q) → ℝ := fun r =>
    familyTransport (selectedBlock N) (blockLength N) (terminalDepth (N + 1))
      (density (terminalDepth (N + 1))) r -
    density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r)
  have hq : 1 ≤ q := (terminalDepth_pos (N + 1)).trans (Nat.le_add_left _ _)
  have hqN : q ≤ 2 * blockLength N := by
    have h := (nextBlockDepth_bounds N).2
    have hN : (0 : ℝ) ≤ blockLength N := by positivity
    have hR : ((blockLength N + terminalDepth (N + 1) : ℕ) : ℝ) ≤ 2 * blockLength N := by linarith
    exact_mod_cast hR
  have heq : familyTransport (selectedPrefixes N) (prefixDepth N) q h
      (M : ZMod (3 ^ (prefixDepth N + q))) =
        selectedDensity (N + 1) (M : ZMod (3 ^ selectedDepth (N + 1))) -
          selectedDensity N (M : ZMod (3 ^ selectedDepth N)) := by
    rw [selectedDensity_integer_evaluation, selectedDensity_integer_evaluation,
      selectedPrefixes_transport_concat]
    rw [familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) q
      (fun _ hw => selectedPrefixes_length hw) h M]
    dsimp [h, q]
    simp_rw [wordTransport_sub, wordTransport_lift]
    rw [Finset.sum_sub_distrib]
  have hnorm := paper_lem_kernel_bound N q hq hqN h
  change ‖familyTransport (selectedPrefixes N) (prefixDepth N) q h‖ ≤
    selectedKernelConstant N * finiteMean (fun x => |h x|) at hnorm
  have herr : finiteMean (fun x => |h x|) ≤
      (2 / 3 : ℝ) * (C6 / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N)) :=
    selected_block_comparison_error C6 hmix N
  have hK : 0 ≤ selectedKernelConstant N := by unfold selectedKernelConstant; positivity
  rw [← heq]
  calc
    |familyTransport (selectedPrefixes N) (prefixDepth N) q h
        (M : ZMod (3 ^ (prefixDepth N + q)))| ≤
        ‖familyTransport (selectedPrefixes N) (prefixDepth N) q h‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_le_pi_norm (familyTransport (selectedPrefixes N) (prefixDepth N) q h)
              (M : ZMod (3 ^ (prefixDepth N + q)))
    _ ≤ selectedKernelConstant N * finiteMean (fun x => |h x|) := hnorm
    _ ≤ selectedKernelConstant N *
        ((2 / 3 : ℝ) * (C6 / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N))) :=
      mul_le_mul_of_nonneg_left herr hK
    _ = selectedIncrementBound C6 N := by unfold selectedIncrementBound; ring

theorem selectedDensity_step_bound (C6 : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * C6 / (m : ℝ) ^ 6)
    (N : ℕ) (hle : selectedDepth N ≤ selectedDepth (N + 1))
    (z : ZMod (3 ^ selectedDepth (N + 1))) :
    |selectedDensity (N + 1) z - selectedDensity N (residueProjection hle z)| ≤
      selectedIncrementBound C6 N := by
  rw [residueProjection_val hle z]
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    selectedDensity_step_bound_integer C6 hmix N (z.val : ℤ)

end SyracuseReport
