import SquareRootProfile
import TerminalBandTransport
import BlockProduct
import SelectedIncrementSummability

/-! Concrete narrower block families. They are subfamilies of the existing
selected prefixes, so all real-offset and arithmetic-kernel bounds persist. -/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def narrowWindow (j : ℕ) : ℕ := min (blockWindow j) (sqrtLogWindow (blockLength j))
noncomputable def narrowBlock (j : ℕ) : Finset Word :=
  terminalBandWords (blockLength j) (narrowWindow j)
noncomputable def narrowPrefixes : ℕ → Finset Word
  | 0 => {Word.nil}
  | j + 1 => (narrowPrefixes j ×ˢ narrowBlock j).image fun p => p.1.concat p.2
noncomputable def narrowPrefixWindow : ℕ → ℕ
  | 0 => 0
  | j + 1 => narrowPrefixWindow j + narrowWindow j
noncomputable def narrowProbability (j : ℕ) : ℝ :=
  terminalBandProbability (blockLength j) (narrowWindow j)
noncomputable def narrowPrefixProbability (N : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, narrowProbability j
noncomputable def narrowDensity (N : ℕ) : ZMod (3 ^ selectedDepth N) → ℝ :=
  familyTransport (narrowPrefixes N) (prefixDepth N) (terminalDepth N) (density (terminalDepth N))

theorem narrowBlock_subset (j : ℕ) : narrowBlock j ⊆ selectedBlock j := by
  intro w hw
  obtain ⟨hlen,hlo,hhi⟩ := (mem_terminalBandWords_iff _ _ _).1 hw
  apply (mem_selectedBlock_iff j w).2
  have hm : narrowWindow j ≤ blockWindow j := Nat.min_le_left _ _
  exact ⟨hlen, by omega, by omega⟩

theorem narrowPrefixes_subset (N : ℕ) : narrowPrefixes N ⊆ selectedPrefixes N := by
  induction N with
  | zero => intro w hw; exact hw
  | succ N ih =>
      exact Finset.image_subset_image (Finset.product_subset_product ih (narrowBlock_subset N))

theorem narrowPrefixes_length {N : ℕ} {w : Word} (hw : w ∈ narrowPrefixes N) :
    w.length = prefixDepth N := selectedPrefixes_length (narrowPrefixes_subset N hw)

theorem narrowPrefixes_total_bounds {N : ℕ} {w : Word} (hw : w ∈ narrowPrefixes N) :
    2 * prefixDepth N ≤ w.total + narrowPrefixWindow N ∧
      w.total ≤ 2 * prefixDepth N + narrowPrefixWindow N := by
  classical
  induction N generalizing w with
  | zero =>
      simp only [narrowPrefixes, Finset.mem_singleton] at hw
      subst w
      simp [prefixDepth, narrowPrefixWindow, Word.total]
  | succ N ih =>
      obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
      have hpu := ih hu
      have hpv := (mem_terminalBandWords_iff _ _ _).1 hv
      simp only [Prod.fst,Prod.snd] at hpu hpv
      simp only [Word.total_concat, prefixDepth, narrowPrefixWindow]
      omega

theorem concat_family_injective (s t : Finset Word) (d b : ℕ)
    (hs : ∀ w ∈ s, w.length = d) (ht : ∀ w ∈ t, w.length = b) :
    Set.InjOn (fun p : Word × Word => p.1.concat p.2) (s ×ˢ t : Finset _) := by
  apply (Word.concat_pair_injective_at_lengths d b).mono
  rintro ⟨u,v⟩ huv
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
  exact ⟨hs u hu,ht v hv⟩

theorem sum_narrowPrefixes_probability (N : ℕ) :
    (∑ w ∈ narrowPrefixes N, w.probability) = narrowPrefixProbability N := by
  classical
  induction N with
  | zero => simp [narrowPrefixes,narrowPrefixProbability,Word.probability]
  | succ N ih =>
      rw [narrowPrefixes, Finset.sum_image (concat_family_injective (narrowPrefixes N) (narrowBlock N) (prefixDepth N)
        (blockLength N) (fun _ hw => narrowPrefixes_length hw)
        (fun _ hw => terminalBandWords_length hw)), Finset.sum_product]
      simp_rw [Word.probability_concat, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ih]
      simp only [narrowPrefixProbability, Finset.prod_range_succ, narrowProbability,
        terminalBandProbability,narrowBlock]

theorem restricted_kernel_bound (N q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ 2 * blockLength N)
    (s : Finset Word) (hs : s ⊆ selectedPrefixes N) (f : ZMod (3 ^ q) → ℝ) :
    ‖familyTransport s (prefixDepth N) q f‖ ≤
      selectedKernelConstant N * finiteMean (fun x => |f x|) := by
  have hbase := paper_lem_residue_count s (prefixDepth N) q
    ((2 : ℝ) ^ (baseBlockLength + 1))
    ((16 : ℝ) ^ baseBlockLength / (16 : ℝ) ^ blockLength N)
    hq (fun _ hw => selectedPrefixes_length (hs hw))
    (fun _ hw => selectedPrefixes_beta_bound (hs hw))
    (fun _ hw => selectedPrefixes_coefficient_bound (hs hw)) f
  have hcard : ((s.image Word.total).card : ℝ) ≤
      4 * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1 := by
    exact (show ((s.image Word.total).card : ℝ) ≤
      ((selectedPrefixes N).image Word.total).card by
        exact_mod_cast Finset.card_le_card (Finset.image_subset_image hs)).trans
      (selectedPrefixes_total_image_card_real N)
  have hc := selectedPrefixes_scaled_coefficient_bound N q hqn
  have hmean : 0 ≤ finiteMean (fun x => |f x|) := by
    unfold finiteMean
    positivity
  apply hbase.trans
  change _ ≤ (4 * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1) *
    ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) * _
  gcongr

theorem concat_family_transport (s t : Finset Word) (d b q : ℕ)
    (hs : ∀ w ∈ s, w.length = d) (ht : ∀ w ∈ t, w.length = b)
    (M : ℤ) (f : ZMod (3 ^ q) → ℝ) :
    (∑ w ∈ (s ×ˢ t).image (fun p => p.1.concat p.2), wordTransport w q M f) =
      ∑ u ∈ s, wordTransport u (b + q) M (familyTransport t b q f) := by
  classical
  rw [Finset.sum_image (concat_family_injective s t d b hs ht), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ v ∈ t, wordTransport (u.concat v) q M f) =
    wordTransport u (b + q) M (fun r => ∑ v ∈ t, wordTransport v q r.val f)
  rw [wordTransport_finset_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [wordTransport_concat_integer]
  change _ = if Contributes u M then u.coefficient *
    wordTransport v q ((inverseInteger u M : ZMod (3 ^ (b + q))).val : ℤ) f else 0
  split_ifs
  · congr 1
    apply wordTransport_congr_residue
    rw [ht v hv]
    simp
  · rfl

theorem narrowDensity_integer_evaluation (N : ℕ) (M : ℤ) :
    narrowDensity N (M : ZMod (3 ^ selectedDepth N)) =
      ∑ w ∈ narrowPrefixes N, wordTransport w (terminalDepth N) M (density (terminalDepth N)) :=
  familyTransport_integer_evaluation _ _ _ (fun _ hw => narrowPrefixes_length hw) _ _

theorem narrowDensity_nonneg (N : ℕ) (r : ZMod (3 ^ selectedDepth N)) :
    0 ≤ narrowDensity N r :=
  Finset.sum_nonneg (fun w _ => wordTransport_density_nonneg w _ _)

theorem narrowDensity_le_density (N : ℕ) (r : ZMod (3 ^ selectedDepth N)) :
    narrowDensity N r ≤ density (selectedDepth N) r :=
  familyTransport_density_le _ _ _ (fun _ hw => narrowPrefixes_length hw) r

theorem narrowDensity_nonunit (N : ℕ) (r : ZMod (3 ^ selectedDepth N)) (hr : ¬ IsUnit r) :
    narrowDensity N r = 0 := by
  exact le_antisymm ((narrowDensity_le_density N r).trans_eq
    (density_nonunit (selectedDepth_positive N) r hr)) (narrowDensity_nonneg N r)

theorem integral_narrowDensity (N : ℕ) :
    (∫ x, cylinderFunction (selectedDepth N) (narrowDensity N) x ∂unitHaar) =
      narrowPrefixProbability N := by
  rw [integral_cylinderFunction_unitHaar (selectedDepth_positive N)
    (narrowDensity N) (narrowDensity_nonunit N)]
  rw [narrowDensity, finiteMean_familyTransport _ _ _
    (fun _ hw => narrowPrefixes_length hw),sum_narrowPrefixes_probability,finiteMean_density]
  ring

theorem narrowWindow_pos (N : ℕ) : 0 < narrowWindow N := by
  exact lt_min (blockWindow_pos N)
    (sqrtLogWindow_bounds ((by norm_num : 2 ≤ 200).trans (blockLength_ge_200 N))).1

theorem narrowProbability_pos (N : ℕ) : 0 < narrowProbability N := terminalBandProbability_pos _ _
theorem narrowProbability_le_one (N : ℕ) : narrowProbability N ≤ 1 := terminalBandProbability_le_one _ _

theorem narrow_rejection_eventually :
    ∀ᶠ N : ℕ in atTop, 1 - narrowProbability N ≤ 2 / (blockLength N : ℝ) ^ 12 := by
  have hwin := blockLength_tendsto_atTop.eventually sqrtLogWindow_le_subpower_eventually
  have hsmall := blockLength_tendsto_atTop.eventually sqrtLogWindow_small_eventually
  filter_upwards [hwin,hsmall] with N hN hS
  have heq : narrowWindow N = sqrtLogWindow (blockLength N) := min_eq_right hN
  have hb : 2 ≤ blockLength N := (by norm_num : 2 ≤ 200).trans (blockLength_ge_200 N)
  have hr := terminalBand_rejection_bound (by omega : 0 < blockLength N)
    (sqrtLogWindow_bounds hb).1 (hS (blockLength N) (by omega))
  change 1 - terminalBandProbability (blockLength N) (narrowWindow N) ≤ _
  rw [heq]
  exact hr.trans (by simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (sqrtLog_rejection_bound hb (by omega) le_rfl) (by norm_num : (0 : ℝ) ≤ 2))

theorem narrowPrefixWindow_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N, (narrowPrefixWindow N : ℝ) ≤ K * sqrtLogProfile (blockLength N) := by
  let r : ℝ := Real.sqrt (201 / 200 : ℝ)
  have hr : 1 < r := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 201 / 200)
    have hn := Real.sqrt_nonneg (201 / 200 : ℝ)
    dsimp [r]
    nlinarith
  have hr0 : 0 < r - 1 := by linarith
  let K : ℝ := 24 / (r - 1)
  have hK : 0 < K := div_pos (by norm_num) hr0
  have hKr : K * r = K + 24 := by dsimp [K]; field_simp [hr0.ne'] <;> ring
  refine ⟨K,hK,?_⟩
  intro N
  induction N with
  | zero => simpa only [narrowPrefixWindow,Nat.cast_zero] using
      mul_nonneg hK.le (sqrtLogProfile_nonneg (blockLength 0))
  | succ N ih =>
      have hm : (narrowWindow N : ℝ) ≤ 24 * sqrtLogProfile (blockLength N) :=
        (show (narrowWindow N : ℝ) ≤ sqrtLogWindow (blockLength N) by
          exact_mod_cast min_le_right (blockWindow N) (sqrtLogWindow (blockLength N))).trans
        (sqrtLogWindow_bounds ((by norm_num : 2 ≤ 200).trans (blockLength_ge_200 N))).2.2
      have hp := mul_le_mul_of_nonneg_left (sqrtLogProfile_block_step N) hK.le
      change K * (r * sqrtLogProfile (blockLength N)) ≤ _ at hp
      rw [← mul_assoc,hKr] at hp
      rw [narrowPrefixWindow,Nat.cast_add]
      linarith

end SyracuseReport
