import SquareRootWords
import CountingCompletion
import SmoothingPrinciple

/-! Positive transport mass for the actual clipped square-root block
construction. No positive-mass producer is assumed. -/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def narrowIncrementBound (C : ℝ) (N : ℕ) : ℝ :=
  selectedIncrementBound C N + (2 / 3 : ℝ) * selectedKernelConstant N * (1 - narrowProbability N)

theorem narrow_weighted_rejection_summable :
    Summable (fun N => (2 / 3 : ℝ) * selectedKernelConstant N * (1 - narrowProbability N)) := by
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  let K : ℝ := (4 / 3 : ℝ) * B
  have hK : 0 ≤ K := by dsimp [K,B]; positivity
  apply (summable_selected_geometric_majorant.mul_left K).of_norm_bounded_eventually_nat
  filter_upwards [narrow_rejection_eventually] with N hr
  have hrej0 : 0 ≤ 1 - narrowProbability N := sub_nonneg.mpr (narrowProbability_le_one N)
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (2 / 3 : ℝ) *
    selectedKernelConstant N * (1 - narrowProbability N) by unfold selectedKernelConstant; positivity)]
  let b : ℝ := blockLength N
  have hb : 1 ≤ b := blockLength_real_ge_one N
  have hbpos : 0 < b := by linarith
  have hp : b ^ (3 / 5 : ℝ) ≤ b := Real.rpow_le_self_of_one_le hb (by norm_num)
  have hkernel : selectedKernelConstant N ≤ (4 * (N : ℝ) + 1) * b * B := by
    unfold selectedKernelConstant
    dsimp [B,b]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * (N : ℝ) by positivity)
    dsimp [b] at hm
    nlinarith
  have hrej : 1 - narrowProbability N ≤ 2 / b ^ 6 := hr.trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ hb (by norm_num : 6 ≤ 12)))
  calc
    _ ≤ (2 / 3 : ℝ) * ((4 * (N : ℝ) + 1) * b * B) * (2 / b ^ 6) := by gcongr
    _ = K * (4 * (N : ℝ) + 1) / b ^ 5 := by dsimp [K]; field_simp [hbpos.ne'] <;> ring
    _ ≤ K * ((4 * (N : ℝ) + 1) * ((200 / 201 : ℝ) ^ 5) ^ N) := by
      have h := blockLength_inverse_fifth_geometric_bound N
      convert mul_le_mul_of_nonneg_left h
        (show 0 ≤ K * (4 * (N : ℝ) + 1) by positivity) using 1 <;> ring

theorem narrow_rejection_summable : Summable (fun N => 1 - narrowProbability N) := by
  apply narrow_weighted_rejection_summable.of_nonneg_of_le
    (fun N => sub_nonneg.mpr (narrowProbability_le_one N))
  intro N
  have hB : (2 : ℝ) ≤ (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength := by
    linarith [(show (1 : ℝ) ≤ (2 : ℝ) ^ (baseBlockLength+1) from one_le_pow₀ (by norm_num)),
      (show (1 : ℝ) ≤ (16 : ℝ) ^ baseBlockLength from one_le_pow₀ (by norm_num))]
  have hK : (2 : ℝ) ≤ selectedKernelConstant N := by
    unfold selectedKernelConstant
    have hp : 0 ≤ 4 * (N : ℝ) * (blockLength N : ℝ) ^ (3 / 5 : ℝ) := by positivity
    nlinarith [mul_nonneg hp (show 0 ≤ (2 : ℝ) ^ (baseBlockLength+1) + (16 : ℝ) ^ baseBlockLength by positivity)]
  have h0 := sub_nonneg.mpr (narrowProbability_le_one N)
  nlinarith [mul_le_mul_of_nonneg_right hK h0]

theorem narrowPrefixProbability_inf_pos : 0 < sInf (Set.range narrowPrefixProbability) :=
  positive_inf_products_of_summable_rejections narrowProbability narrowProbability_pos
    narrowProbability_le_one narrow_rejection_summable

theorem narrowIncrementBound_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ narrowIncrementBound C N := by
  have hs := selectedIncrementBound_nonneg hC blockProbability_le_one N
  have hr := sub_nonneg.mpr (narrowProbability_le_one N)
  unfold narrowIncrementBound selectedKernelConstant
  positivity

theorem narrowIncrementBound_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (narrowIncrementBound C) :=
  (summable_selectedIncrementBound hC blockProbability_le_one block_rejection_bound).add
    narrow_weighted_rejection_summable

theorem narrow_block_comparison (C : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤ (2 / 3 : ℝ) * C / (m : ℝ) ^ 6)
    (N : ℕ) :
    finiteMean (fun r : ZMod (3 ^ (blockLength N + terminalDepth (N+1))) =>
      |familyTransport (narrowBlock N) (blockLength N) (terminalDepth (N+1))
        (density (terminalDepth (N+1))) r -
        density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r)|) ≤
      (2 / 3 : ℝ) * (C / (terminalDepth N : ℝ) ^ 6 + (1 - narrowProbability N)) := by
  have hmass : finiteMean (fun r : ZMod (3 ^ (blockLength N + terminalDepth (N+1))) =>
      density (blockLength N + terminalDepth (N+1)) r -
        familyTransport (narrowBlock N) (blockLength N) (terminalDepth (N+1))
          (density (terminalDepth (N+1))) r) = (2 / 3 : ℝ) * (1 - narrowProbability N) := by
    rw [finiteMean_subtract,finiteMean_density,finiteMean_familyTransport (narrowBlock N) (blockLength N) (terminalDepth (N+1))
      (fun _ hw => terminalBandWords_length hw) (density (terminalDepth (N+1))),finiteMean_density]
    unfold narrowProbability terminalBandProbability narrowBlock
    ring
  have h := block_error_bound
    (familyTransport (narrowBlock N) (blockLength N) (terminalDepth (N+1)) (density (terminalDepth (N+1))))
    (density (blockLength N + terminalDepth (N+1)))
    (fun r => density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r))
    ((2 / 3 : ℝ) * (1 - narrowProbability N)) ((2 / 3 : ℝ) * C / (terminalDepth N : ℝ) ^ 6)
    (fun r => familyTransport_density_le _ _ _ (fun _ hw => terminalBandWords_length hw) r)
    hmass.le (hmix _ _ (terminalDepth_pos N) (nextBlockDepth_bounds N).1)
  convert h using 1
  ring

theorem narrowDensity_step (C : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤ (2 / 3 : ℝ) * C / (m : ℝ) ^ 6)
    (N : ℕ) (M : ℤ) :
    |narrowDensity (N+1) (M : ZMod (3 ^ selectedDepth (N+1))) -
      narrowDensity N (M : ZMod (3 ^ selectedDepth N))| ≤ narrowIncrementBound C N := by
  classical
  let q := blockLength N + terminalDepth (N+1)
  let f : ZMod (3 ^ q) → ℝ := fun r =>
    familyTransport (narrowBlock N) (blockLength N) (terminalDepth (N+1)) (density (terminalDepth (N+1))) r -
      density (terminalDepth N) (residueProjection (nextBlockDepth_bounds N).1 r)
  have hq : 1 ≤ q := (terminalDepth_pos (N+1)).trans (Nat.le_add_left _ _)
  have hqN : q ≤ 2 * blockLength N := by
    have h := (nextBlockDepth_bounds N).2
    have hR : ((blockLength N + terminalDepth (N+1) : ℕ) : ℝ) ≤ 2 * blockLength N := by
      have hb : (0 : ℝ) ≤ blockLength N := by positivity
      linarith
    exact_mod_cast hR
  have heq : familyTransport (narrowPrefixes N) (prefixDepth N) q f
      (M : ZMod (3 ^ (prefixDepth N + q))) =
        narrowDensity (N+1) (M : ZMod (3 ^ selectedDepth (N+1))) -
          narrowDensity N (M : ZMod (3 ^ selectedDepth N)) := by
    rw [narrowDensity_integer_evaluation,narrowDensity_integer_evaluation,narrowPrefixes,
      concat_family_transport (narrowPrefixes N) (narrowBlock N) (prefixDepth N) (blockLength N) (terminalDepth (N+1))
        (fun _ hw => narrowPrefixes_length hw) (fun _ hw => terminalBandWords_length hw)]
    rw [familyTransport_integer_evaluation _ _ _ (fun _ hw => narrowPrefixes_length hw) f M]
    dsimp [f,q]
    simp_rw [wordTransport_sub,wordTransport_lift]
    rw [Finset.sum_sub_distrib]
  have hnorm := restricted_kernel_bound N q hq hqN (narrowPrefixes N) (narrowPrefixes_subset N) f
  have herr := narrow_block_comparison C hmix N
  have hK : 0 ≤ selectedKernelConstant N := by unfold selectedKernelConstant; positivity
  rw [← heq]
  calc
    _ ≤ ‖familyTransport (narrowPrefixes N) (prefixDepth N) q f‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (familyTransport (narrowPrefixes N) (prefixDepth N) q f) (M : ZMod (3 ^ (prefixDepth N+q)))
    _ ≤ selectedKernelConstant N * finiteMean (fun r => |f r|) := hnorm
    _ ≤ selectedKernelConstant N * ((2 / 3 : ℝ) *
        (C / (terminalDepth N : ℝ) ^ 6 + (1 - narrowProbability N))) :=
      mul_le_mul_of_nonneg_left herr hK
    _ = selectedKernelConstant N * ((2 / 3 : ℝ) * C / (terminalDepth N : ℝ) ^ 6) +
        (2 / 3 : ℝ) * selectedKernelConstant N * (1 - narrowProbability N) := by ring
    _ ≤ narrowIncrementBound C N := add_le_add
      (selected_mixing_bound_le_increment C blockProbability_le_one N) le_rfl

noncomputable def narrowFlexibleDensity (N t : ℕ) : ZMod (3 ^ (prefixDepth N + t)) → ℝ :=
  familyTransport (narrowPrefixes N) (prefixDepth N) t (density t)

theorem narrowFlexible_comparison (C : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤ (2 / 3 : ℝ) * C / (m : ℝ) ^ 6)
    (N t : ℕ) (hkt : terminalDepth N ≤ t) (ht : t ≤ 2 * blockLength N) (M : ℤ) :
    |narrowFlexibleDensity N t (M : ZMod (3 ^ (prefixDepth N+t))) -
      narrowDensity N (M : ZMod (3 ^ selectedDepth N))| ≤ narrowIncrementBound C N := by
  classical
  let f : ZMod (3 ^ t) → ℝ := fun r => density t r - density (terminalDepth N) (residueProjection hkt r)
  have heq : familyTransport (narrowPrefixes N) (prefixDepth N) t f
      (M : ZMod (3 ^ (prefixDepth N+t))) =
        narrowFlexibleDensity N t (M : ZMod (3 ^ (prefixDepth N+t))) -
          narrowDensity N (M : ZMod (3 ^ selectedDepth N)) := by
    rw [familyTransport_integer_evaluation _ _ _ (fun _ hw => narrowPrefixes_length hw) f M,
      narrowDensity_integer_evaluation]
    change (∑ w ∈ narrowPrefixes N, wordTransport w t M f) =
      familyTransport (narrowPrefixes N) (prefixDepth N) t (density t) _ - _
    rw [familyTransport_integer_evaluation _ _ _ (fun _ hw => narrowPrefixes_length hw) (density t) M]
    dsimp [f]
    simp_rw [wordTransport_sub,wordTransport_lift]
    rw [Finset.sum_sub_distrib]
  have hnorm := restricted_kernel_bound N t ((terminalDepth_pos N).trans hkt) ht
    (narrowPrefixes N) (narrowPrefixes_subset N) f
  have hK : 0 ≤ selectedKernelConstant N := by unfold selectedKernelConstant; positivity
  rw [← heq]
  calc
    _ ≤ ‖familyTransport (narrowPrefixes N) (prefixDepth N) t f‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (familyTransport (narrowPrefixes N) (prefixDepth N) t f) (M : ZMod (3 ^ (prefixDepth N+t)))
    _ ≤ selectedKernelConstant N * finiteMean (fun r => |f r|) := hnorm
    _ ≤ selectedKernelConstant N * ((2 / 3 : ℝ) * C / (terminalDepth N : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (hmix _ _ (terminalDepth_pos N) hkt) hK
    _ ≤ selectedIncrementBound C N := selected_mixing_bound_le_increment C blockProbability_le_one N
    _ ≤ narrowIncrementBound C N := by
      have h0 := sub_nonneg.mpr (narrowProbability_le_one N)
      unfold narrowIncrementBound
      apply le_add_of_nonneg_right
      unfold selectedKernelConstant
      positivity

theorem narrowDensity_positive_cylinder :
    ∃ (N0 q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ N0 ∧ 1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ N : ℕ, N0 ≤ N → ∀ R : ℤ, (R : ZMod (3 ^ q)) = y →
        kappa ≤ narrowDensity N (R : ZMod (3 ^ selectedDepth N)) := by
  obtain ⟨C,hC,hmix⟩ := paper_thm_mixing 6 (by norm_num)
  let a := sInf (Set.range narrowPrefixProbability)
  have ha : 0 < a := narrowPrefixProbability_inf_pos
  have hs := narrowIncrementBound_summable hC
  have htail : Tendsto (fun N => ∑' j : ℕ, narrowIncrementBound C (N+j)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (narrowIncrementBound C)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (htail.eventually (eventually_lt_nhds (show 0 < a/2 by linarith)))
  let N0 := max K 1
  obtain ⟨y,hy,hmark⟩ := exists_unit_ge_integral_cylinderFunction
    (selectedDepth N0) (selectedDepth_positive N0) (narrowDensity N0)
  rw [integral_narrowDensity] at hmark
  have haN : a ≤ narrowPrefixProbability N0 := csInf_le
    ⟨0,by rintro _ ⟨j,rfl⟩; exact (Finset.prod_nonneg (fun i _ => (narrowProbability_pos i).le))⟩ ⟨N0,rfl⟩
  refine ⟨N0,selectedDepth N0,y,a/2,le_max_right _ _,selectedDepth_positive N0,hy,by linarith,?_⟩
  intro N hN R hRy
  have hd := selected_uniform_tail
    (fun j (M : ℤ) => narrowDensity j (M : ZMod (3 ^ selectedDepth j)))
    (narrowIncrementBound C) hs (narrowIncrementBound_nonneg hC) (narrowDensity_step C hmix)
    N0 N hN R
  change |narrowDensity N (R : ZMod (3 ^ selectedDepth N)) -
    narrowDensity N0 (R : ZMod (3 ^ selectedDepth N0))| ≤ _ at hd
  rw [hRy] at hd
  have hsmall := hK N0 (le_max_left _ _)
  have hlo := (abs_le.mp hd).1
  linarith

theorem narrowFlexible_positive_cylinder :
    ∃ (N0 q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ N0 ∧ 1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ N : ℕ, N0 ≤ N → ∀ t : ℕ, terminalDepth N ≤ t → t ≤ 2 * blockLength N →
        ∀ R : ℤ, (R : ZMod (3 ^ q)) = y →
          kappa ≤ narrowFlexibleDensity N t (R : ZMod (3 ^ (prefixDepth N+t))) := by
  obtain ⟨L,q,y,kappa,hL,hq,hy,hk,hpositive⟩ := narrowDensity_positive_cylinder
  obtain ⟨C,hC,hmix⟩ := paper_thm_mixing 6 (by norm_num)
  have hs := narrowIncrementBound_summable hC
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hs.tendsto_atTop_zero.eventually (eventually_lt_nhds (show 0 < kappa/2 by linarith)))
  refine ⟨max L K,q,y,kappa/2,hL.trans (le_max_left _ _),hq,hy,by linarith,?_⟩
  intro N hN t hkt ht R hRy
  have hpos := hpositive N ((le_max_left _ _).trans hN) R hRy
  have herr := narrowFlexible_comparison C hmix N t hkt ht R
  have hsmall := hK N ((le_max_right _ _).trans hN)
  have hlo := (abs_le.mp herr).1
  linarith

end SyracuseReport
