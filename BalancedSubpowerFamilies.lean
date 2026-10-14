import QuantitativeFamilies

/-! Positive transport mass in concrete subpower-balanced families at every
large length. No family-existence or positive-mass hypothesis is imported. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem subpower_pruning_error_eventually {kappa : ℝ} (hk : 0 < kappa) :
    ∀ᶠ h : ℕ in atTop, ∀ N t : ℕ,
      h = prefixDepth N + t → terminalDepth N ≤ t → t ≤ 2 * blockLength N →
      ∀ R : ℤ,
      |(∑ w ∈ terminalPrunedPrefixes N t (subpowerWindow h),
          wordTransport w 0 R (density 0)) -
        familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
          (R : ZMod (3 ^ (prefixDepth N + t)))| ≤ kappa := by
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  have hlim : Tendsto (fun h : ℕ => (4 / 3 : ℝ) * B *
      ((32 * (h : ℝ) ^ 2 + 1) * Real.exp (-((h : ℝ) ^ (1 / 5 : ℝ)) / 12)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using subpower_pruning_envelope_tendsto.const_mul ((4 / 3 : ℝ) * B)
  have hev := hlim.eventually (eventually_lt_nhds hk)
  filter_upwards [hev, subpowerWindow_small_eventually, eventually_ge_atTop 1]
    with h henv hsmall hh
  intro N t hlen hkt htN R
  have ht : 0 < t := lt_of_lt_of_le (terminalDepth_pos N) hkt
  have hth : t ≤ h := by omega
  have hlength : h ≤ 1616 * t := by
    rw [hlen]
    exact flexible_length_le_terminal N t hkt htN
  have herr := terminalPruning_exponential_error N t (subpowerWindow h)
    ht (subpowerWindow_bounds h hh).1 htN (hsmall t hlength) R
  have hkernel := selectedKernelConstant_quadratic_length_bound N t hkt
  rw [← hlen] at hkernel
  have hexp := Real.exp_le_exp.mpr (subpower_rejection_exponent ht hth)
  calc
    _ ≤ _ := herr
    _ ≤ (4 / 3 : ℝ) * ((32 * (h : ℝ) ^ 2 + 1) * B) *
        Real.exp (-((h : ℝ) ^ (1 / 5 : ℝ)) / 12) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hkernel (by norm_num)) hexp
        (Real.exp_pos _).le (by dsimp [B]; positivity)
    _ = _ := by ring
    _ ≤ kappa := henv.le

def SubpowerBalancedFamilies : Prop :=
  ∃ (q : ℕ) (y : ZMod (3 ^ q)) (kappa B K : ℝ) (H : ℕ),
    1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧ 0 < B ∧ 0 < K ∧ 1 ≤ H ∧
    ∀ h : ℕ, H ≤ h → ∀ R : ℤ, (R : ZMod (3 ^ q)) = y →
      ∃ V : Finset Word,
        (∀ w ∈ V, w.length = h ∧ Contributes w R ∧ w.beta ≤ B ∧
          2 * (h : ℝ) - K * (h : ℝ) ^ (3 / 5 : ℝ) ≤ (w.total : ℝ) ∧
          (w.total : ℝ) ≤ 2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ)) ∧
        ((V.image Word.total).card : ℝ) ≤ (2 * K + 1) * ((h : ℝ) + 1) ∧
        kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0)

theorem subpower_balanced_families : SubpowerBalancedFamilies := by
  classical
  obtain ⟨N0, q, y, kappa, hN0, hq, hy, hk, hpositive⟩ :=
    flexibleSelectedDensity_positive_cylinder
  obtain ⟨K, hK, hprefix⟩ := prefixWindow_power_bound
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  let K' : ℝ := K * (8 : ℝ) ^ (3 / 5 : ℝ) + 2
  have hK' : 0 < K' := by dsimp [K']; positivity
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (subpower_pruning_error_eventually (show 0 < kappa / 2 by linarith))
  let H := max 1 (max (selectedDepth N0) P)
  refine ⟨q, y, kappa / 2, B, K', H, hq, hy, by linarith,
    by dsimp [B]; positivity, hK', le_max_left _ _, ?_⟩
  intro h hh R hRy
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hdepth : selectedDepth N0 ≤ h :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hh)
  have hPh : P ≤ h := (le_max_right _ _).trans ((le_max_right _ _).trans hh)
  obtain ⟨N, t, hN0N, hlen, hkt, htupper⟩ := exists_flexible_selected_depth N0 h hdepth
  have htN : t ≤ 2 * blockLength N := by
    have hu := (nextBlockDepth_bounds N).2
    have hupperR : ((blockLength N + terminalDepth (N + 1) : ℕ) : ℝ) ≤
        2 * blockLength N := by
      have hb : (0 : ℝ) ≤ blockLength N := by positivity
      linarith
    have hupperNat : blockLength N + terminalDepth (N + 1) ≤ 2 * blockLength N := by
      exact_mod_cast hupperR
    exact htupper.trans hupperNat
  have hblock : (blockLength N : ℝ) ≤ 8 * h := by
    have ht := (terminalDepth_real_bounds N).1
    have htR : (terminalDepth N : ℝ) ≤ t := by exact_mod_cast hkt
    have hthR : (t : ℝ) ≤ h := by exact_mod_cast (show t ≤ h by omega)
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ blockLength N)
    hblock (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
  have hprefix' := (hprefix N).trans (mul_le_mul_of_nonneg_left hpow hK.le)
  have hm := (subpowerWindow_bounds h hh1).2.2
  have hwindow : (prefixWindow N + subpowerWindow h : ℝ) ≤
      K' * (h : ℝ) ^ (3 / 5 : ℝ) := by
    dsimp [K']
    nlinarith
  let V := contributingPrunedPrefixes N t (subpowerWindow h) R
  have hprops := contributingPrunedPrefixes_properties N t (subpowerWindow h) R htN
  refine ⟨V, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwlen, hc, hb, hlo, hhi⟩ := hprops.1 w hw
    rw [← hlen] at hwlen hlo hhi
    have hloR : 2 * (h : ℝ) ≤ (w.total : ℝ) + (prefixWindow N + subpowerWindow h : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (w.total : ℝ) ≤ 2 * (h : ℝ) + (prefixWindow N + subpowerWindow h : ℝ) := by
      exact_mod_cast hhi
    exact ⟨hwlen, hc, hb, by linarith, by linarith⟩
  · have hcardR : ((V.image Word.total).card : ℝ) ≤
        2 * (prefixWindow N + subpowerWindow h : ℝ) + 1 := by exact_mod_cast hprops.2
    have hsmall : (h : ℝ) ^ (3 / 5 : ℝ) ≤ h :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast hh1) (by norm_num)
    have hKpow := mul_le_mul_of_nonneg_left hsmall hK'.le
    have hhR : (0 : ℝ) ≤ h := by positivity
    nlinarith
  · dsimp [V]
    rw [contributingPrunedPrefixes_mass]
    have hpos := (hpositive N hN0N).2 t hkt htN R hRy
    have herr := hP h hPh N t hlen hkt htN R
    change kappa ≤ familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
      (R : ZMod (3 ^ (prefixDepth N + t))) at hpos
    have hlo := (abs_le.mp herr).1
    linarith

end SyracuseReport
