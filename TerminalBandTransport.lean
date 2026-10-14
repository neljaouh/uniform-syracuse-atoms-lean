import TerminalBandAcceptance
import SelectedDensityIncrement
set_option backward.isDefEq.respectTransparency false

/-! Terminal pruning of selected prefixes, with its exact rejected mass,
uniform transport error, and affine offset bound. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def terminalBandDensity (t m : ℕ) : ZMod (3 ^ t) → ℝ :=
  familyTransport (terminalBandWords t m) t 0 (density 0)

theorem terminalBandDensity_nonneg (t m : ℕ) (r : ZMod (3 ^ t)) :
    0 ≤ terminalBandDensity t m r := by
  classical
  exact Finset.sum_nonneg (fun w _ => wordTransport_density_nonneg w 0 (r.val : ℤ))

theorem terminalBandDensity_le_density (t m : ℕ) (r : ZMod (3 ^ t)) :
    terminalBandDensity t m r ≤ density t r :=
  familyTransport_density_le (terminalBandWords t m) t 0
    (fun _ hw => terminalBandWords_length hw) r

theorem finiteMean_terminalBandDensity (t m : ℕ) :
    finiteMean (terminalBandDensity t m) = (2 / 3 : ℝ) * terminalBandProbability t m := by
  rw [terminalBandDensity, finiteMean_familyTransport (terminalBandWords t m) t 0
    (fun _ hw => terminalBandWords_length hw) (density 0), finiteMean_density]
  unfold terminalBandProbability
  ring

theorem terminalBandDensity_rejected_mass (t m : ℕ) :
    finiteMean (fun r : ZMod (3 ^ t) => density t r - terminalBandDensity t m r) =
      (2 / 3 : ℝ) * (1 - terminalBandProbability t m) := by
  rw [finiteMean_subtract, finiteMean_density, finiteMean_terminalBandDensity]
  ring

theorem terminalBandDensity_abs_error (t m : ℕ) :
    finiteMean (fun r : ZMod (3 ^ t) => |terminalBandDensity t m r - density t r|) =
      (2 / 3 : ℝ) * (1 - terminalBandProbability t m) := by
  have heq : (fun r : ZMod (3 ^ t) => |terminalBandDensity t m r - density t r|) =
      (fun r => density t r - terminalBandDensity t m r) := by
    funext r
    rw [abs_of_nonpos (sub_nonpos.mpr (terminalBandDensity_le_density t m r))]
    ring
  rw [heq, terminalBandDensity_rejected_mass]

noncomputable def terminalPrunedPrefixes (N t m : ℕ) : Finset Word := by
  classical
  exact (selectedPrefixes N ×ˢ terminalBandWords t m).image fun p => p.1.concat p.2

theorem terminalPrunedPrefixes_length {N t m : ℕ} {w : Word}
    (hw : w ∈ terminalPrunedPrefixes N t m) : w.length = prefixDepth N + t := by
  classical
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  simp only [Word.length_concat, selectedPrefixes_length hu, terminalBandWords_length hv]

theorem terminalPrunedPrefixes_total_bounds {N t m : ℕ} {w : Word}
    (hw : w ∈ terminalPrunedPrefixes N t m) :
    2 * (prefixDepth N + t) ≤ w.total + (prefixWindow N + m) ∧
      w.total ≤ 2 * (prefixDepth N + t) + (prefixWindow N + m) := by
  classical
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have huA := selectedPrefixes_total_bounds hu
  have hvA := (mem_terminalBandWords_iff t m v).mp hv
  simp only [Prod.fst, Prod.snd] at huA hvA
  simp only [Word.total_concat]
  omega

theorem terminalPrunedPrefixes_total_image_card (N t m : ℕ) :
    ((terminalPrunedPrefixes N t m).image Word.total).card ≤
      2 * (prefixWindow N + m) + 1 := by
  classical
  let lo := 2 * (prefixDepth N + t) - (prefixWindow N + m)
  let hi := 2 * (prefixDepth N + t) + (prefixWindow N + m)
  have hsub : (terminalPrunedPrefixes N t m).image Word.total ⊆ Finset.Icc lo hi := by
    intro A hA
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hA
    have hbounds := terminalPrunedPrefixes_total_bounds hw
    exact Finset.mem_Icc.mpr ⟨by dsimp [lo]; omega, hbounds.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  dsimp [lo, hi] at hcard
  omega

theorem terminalPrunedPrefixes_concat_injective (N t m : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1.concat p.2)
      (selectedPrefixes N ×ˢ terminalBandWords t m : Finset (Word × Word)) := by
  apply (Word.concat_pair_injective_at_lengths (prefixDepth N) t).mono
  rintro ⟨u, v⟩ huv
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  exact ⟨selectedPrefixes_length hu, terminalBandWords_length hv⟩

theorem terminalPrunedPrefixes_transport_integer (N t m : ℕ) (M : ℤ) :
    (∑ w ∈ terminalPrunedPrefixes N t m, wordTransport w 0 M (density 0)) =
      ∑ u ∈ selectedPrefixes N, wordTransport u t M (terminalBandDensity t m) := by
  classical
  rw [terminalPrunedPrefixes, Finset.sum_image (terminalPrunedPrefixes_concat_injective N t m),
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ v ∈ terminalBandWords t m, wordTransport (u.concat v) 0 M (density 0)) =
    wordTransport u t M
      (fun r => ∑ v ∈ terminalBandWords t m, wordTransport v 0 r.val (density 0))
  rw [wordTransport_finset_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [wordTransport_concat_integer]
  change _ = if Contributes u M then u.coefficient *
    wordTransport v 0 ((inverseInteger u M : ZMod (3 ^ t)).val : ℤ) (density 0) else 0
  split_ifs
  · congr 1
    apply wordTransport_congr_residue
    rw [terminalBandWords_length hv]
    simp
  · rfl

theorem terminalPrunedPrefixes_beta_bound {N t m : ℕ} (ht : t ≤ 2 * blockLength N)
    {w : Word} (hw : w ∈ terminalPrunedPrefixes N t m) :
    w.beta ≤ (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength := by
  classical
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have huB := selectedPrefixes_beta_bound hu
  have huC := selectedPrefixes_coefficient_scaled hu
  have hvB : v.beta ≤ (2 : ℝ) ^ t := by
    simpa only [terminalBandWords_length hv] using v.beta_le_two_pow_length
  have htB : (2 : ℝ) ^ t ≤ (16 : ℝ) ^ blockLength N := by
    calc
      (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (2 * blockLength N) := pow_le_pow_right₀ (by norm_num) ht
      _ = (4 : ℝ) ^ blockLength N := by rw [pow_mul]; norm_num
      _ ≤ (16 : ℝ) ^ blockLength N := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hvC := mul_le_mul_of_nonneg_left (hvB.trans htB) u.coefficient_pos.le
  rw [Word.beta_concat]
  exact add_le_add huB (hvC.trans huC)

theorem terminalPruning_transport_error (N t m : ℕ) (ht : 1 ≤ t)
    (htN : t ≤ 2 * blockLength N) (M : ℤ) :
    |(∑ w ∈ terminalPrunedPrefixes N t m, wordTransport w 0 M (density 0)) -
      familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
        (M : ZMod (3 ^ (prefixDepth N + t)))| ≤
      (2 / 3 : ℝ) * selectedKernelConstant N * (1 - terminalBandProbability t m) := by
  classical
  let f : ZMod (3 ^ t) → ℝ := fun r => terminalBandDensity t m r - density t r
  have heq : familyTransport (selectedPrefixes N) (prefixDepth N) t f
      (M : ZMod (3 ^ (prefixDepth N + t))) =
      (∑ w ∈ terminalPrunedPrefixes N t m, wordTransport w 0 M (density 0)) -
        familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
          (M : ZMod (3 ^ (prefixDepth N + t))) := by
    rw [terminalPrunedPrefixes_transport_integer,
      familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) t
        (fun _ hw => selectedPrefixes_length hw) f M,
      familyTransport_integer_evaluation (selectedPrefixes N) (prefixDepth N) t
        (fun _ hw => selectedPrefixes_length hw) (density t) M]
    dsimp [f]
    simp_rw [wordTransport_sub]
    rw [Finset.sum_sub_distrib]
  have hnorm := paper_lem_kernel_bound N t ht htN f
  change ‖familyTransport (selectedPrefixes N) (prefixDepth N) t f‖ ≤
    selectedKernelConstant N * finiteMean (fun r => |f r|) at hnorm
  have hmass : finiteMean (fun r => |f r|) =
      (2 / 3 : ℝ) * (1 - terminalBandProbability t m) := terminalBandDensity_abs_error t m
  rw [hmass] at hnorm
  rw [← heq]
  have hp : |familyTransport (selectedPrefixes N) (prefixDepth N) t f
      (M : ZMod (3 ^ (prefixDepth N + t)))| ≤
      ‖familyTransport (selectedPrefixes N) (prefixDepth N) t f‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm
      (familyTransport (selectedPrefixes N) (prefixDepth N) t f)
      (M : ZMod (3 ^ (prefixDepth N + t)))
  convert hp.trans hnorm using 1
  ring

theorem terminalPruning_exponential_error (N t m : ℕ) (ht : 0 < t) (hm : 0 < m)
    (htN : t ≤ 2 * blockLength N) (hsmall : (m : ℝ) ≤ (3 / 2 : ℝ) * t) (M : ℤ) :
    |(∑ w ∈ terminalPrunedPrefixes N t m, wordTransport w 0 M (density 0)) -
      familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
        (M : ZMod (3 ^ (prefixDepth N + t)))| ≤
      (4 / 3 : ℝ) * selectedKernelConstant N * Real.exp (-((m : ℝ) ^ 2) / (12 * (t : ℝ))) := by
  have h := terminalPruning_transport_error N t m ht htN M
  have hK : 0 ≤ (2 / 3 : ℝ) * selectedKernelConstant N := by
    unfold selectedKernelConstant
    positivity
  have hr := mul_le_mul_of_nonneg_left (terminalBand_rejection_bound ht hm hsmall) hK
  convert h.trans hr using 1
  ring

end SyracuseReport
