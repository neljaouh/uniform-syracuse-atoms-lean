import SquareRootConstruction

/-! All-length admissible inverse-word families in square-root logarithmic
valuation windows, with positive mass proved by the narrower construction. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def narrowPrunedPrefixes (N t m : ℕ) : Finset Word := by
  classical
  exact (narrowPrefixes N ×ˢ terminalBandWords t m).image fun p => p.1.concat p.2

theorem narrowPrunedPrefixes_subset (N t m : ℕ) :
    narrowPrunedPrefixes N t m ⊆ terminalPrunedPrefixes N t m :=
  Finset.image_subset_image (Finset.product_subset_product (narrowPrefixes_subset N) (by intro w hw; exact hw))

theorem narrowPrunedPrefixes_total_bounds {N t m : ℕ} {w : Word}
    (hw : w ∈ narrowPrunedPrefixes N t m) :
    2 * (prefixDepth N+t) ≤ w.total + (narrowPrefixWindow N+m) ∧
      w.total ≤ 2 * (prefixDepth N+t) + (narrowPrefixWindow N+m) := by
  classical
  obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
  have hpu := narrowPrefixes_total_bounds hu
  have hpv := (mem_terminalBandWords_iff _ _ _).1 hv
  simp only [Prod.fst,Prod.snd] at hpu hpv
  simp only [Word.total_concat]
  omega

theorem narrowPrunedPrefixes_image_card (N t m : ℕ) :
    ((narrowPrunedPrefixes N t m).image Word.total).card ≤ 2 * (narrowPrefixWindow N+m)+1 := by
  classical
  let lo := 2 * (prefixDepth N+t) - (narrowPrefixWindow N+m)
  let hi := 2 * (prefixDepth N+t) + (narrowPrefixWindow N+m)
  have hsub : (narrowPrunedPrefixes N t m).image Word.total ⊆ Finset.Icc lo hi := by
    intro A hA
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
    have hb := narrowPrunedPrefixes_total_bounds hw
    exact Finset.mem_Icc.mpr ⟨by dsimp [lo]; omega,hb.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  dsimp [lo,hi] at hc
  omega

theorem narrowPrunedPrefixes_transport (N t m : ℕ) (R : ℤ) :
    (∑ w ∈ narrowPrunedPrefixes N t m,wordTransport w 0 R (density 0)) =
      ∑ w ∈ narrowPrefixes N,wordTransport w t R (terminalBandDensity t m) := by
  simpa only [Nat.add_zero] using concat_family_transport (narrowPrefixes N)
    (terminalBandWords t m) (prefixDepth N) t 0 (fun _ hw => narrowPrefixes_length hw)
    (fun _ hw => terminalBandWords_length hw) R (density 0)

theorem narrowPruning_error (N t m : ℕ) (ht : 0 < t) (hm : 0 < m)
    (htN : t ≤ 2 * blockLength N) (hsmall : (m : ℝ) ≤ (3/2 : ℝ)*t) (R : ℤ) :
    |(∑ w ∈ narrowPrunedPrefixes N t m,wordTransport w 0 R (density 0)) -
      narrowFlexibleDensity N t (R : ZMod (3 ^ (prefixDepth N+t)))| ≤
      (4/3 : ℝ) * selectedKernelConstant N * Real.exp (-((m : ℝ)^2)/(12*(t : ℝ))) := by
  classical
  let f : ZMod (3 ^ t) → ℝ := fun r => terminalBandDensity t m r - density t r
  have heq : familyTransport (narrowPrefixes N) (prefixDepth N) t f
      (R : ZMod (3 ^ (prefixDepth N+t))) =
        (∑ w ∈ narrowPrunedPrefixes N t m,wordTransport w 0 R (density 0)) -
          narrowFlexibleDensity N t (R : ZMod (3 ^ (prefixDepth N+t))) := by
    rw [narrowPrunedPrefixes_transport,familyTransport_integer_evaluation _ _ _
      (fun _ hw => narrowPrefixes_length hw) f R]
    change (∑ w ∈ narrowPrefixes N,wordTransport w t R f) = _ -
      familyTransport (narrowPrefixes N) (prefixDepth N) t (density t) _
    rw [familyTransport_integer_evaluation _ _ _ (fun _ hw => narrowPrefixes_length hw) (density t) R]
    dsimp [f]
    simp_rw [wordTransport_sub]
    rw [Finset.sum_sub_distrib]
  have hnorm := restricted_kernel_bound N t ht htN (narrowPrefixes N) (narrowPrefixes_subset N) f
  have hmean : finiteMean (fun r => |f r|) = (2/3 : ℝ)*(1-terminalBandProbability t m) :=
    terminalBandDensity_abs_error t m
  rw [hmean] at hnorm
  rw [← heq]
  have hp : |familyTransport (narrowPrefixes N) (prefixDepth N) t f
      (R : ZMod (3 ^ (prefixDepth N+t)))| ≤ ‖familyTransport (narrowPrefixes N) (prefixDepth N) t f‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm
      (familyTransport (narrowPrefixes N) (prefixDepth N) t f) (R : ZMod (3 ^ (prefixDepth N+t)))
  have hK : 0 ≤ selectedKernelConstant N * (2/3 : ℝ) := by unfold selectedKernelConstant; positivity
  have hr := mul_le_mul_of_nonneg_left (terminalBand_rejection_bound ht hm hsmall) hK
  exact (hp.trans hnorm).trans (by convert hr using 1 <;> ring)

theorem sqrtLog_pruning_envelope_tendsto :
    Tendsto (fun h : ℕ => (32*(h : ℝ)^2+1)/(h : ℝ)^12) atTop (𝓝 0) := by
  have h10 : Tendsto (fun h : ℕ => 1/(h : ℝ)^10) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<10)).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext h
    dsimp only [Function.comp_apply]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ h),Real.rpow_ofNat]
    simp only [one_div]
  have h12 : Tendsto (fun h : ℕ => 1/(h : ℝ)^12) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<12)).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext h
    dsimp only [Function.comp_apply]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ h),Real.rpow_ofNat]
    simp only [one_div]
  have hs := (h10.const_mul 32).add h12
  simp only [mul_zero,zero_add] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hp : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  field_simp [hp] <;> ring

theorem narrowPruning_eventually {kappa : ℝ} (hk : 0 < kappa) :
    ∀ᶠ h : ℕ in atTop, ∀ N t : ℕ, h = prefixDepth N+t →
      terminalDepth N ≤ t → t ≤ 2*blockLength N → ∀ R : ℤ,
      |(∑ w ∈ narrowPrunedPrefixes N t (sqrtLogWindow h),wordTransport w 0 R (density 0)) -
        narrowFlexibleDensity N t (R : ZMod (3 ^ (prefixDepth N+t)))| ≤ kappa := by
  let B : ℝ := (2 : ℝ)^(baseBlockLength+1)+(16 : ℝ)^baseBlockLength
  have hlim := sqrtLog_pruning_envelope_tendsto.const_mul ((4/3 : ℝ)*B)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_lt_nhds hk),sqrtLogWindow_small_eventually,
    eventually_ge_atTop 2] with h he hsmall hh
  intro N t hlen hkt htN R
  have ht : 0<t := lt_of_lt_of_le (terminalDepth_pos N) hkt
  have hth : t≤h := by omega
  have hlength : h≤1616*t := by rw [hlen]; exact flexible_length_le_terminal N t hkt htN
  have herr := narrowPruning_error N t (sqrtLogWindow h) ht (sqrtLogWindow_bounds hh).1 htN (hsmall t hlength) R
  have hkernel := selectedKernelConstant_quadratic_length_bound N t hkt
  rw [← hlen] at hkernel
  have hexp := sqrtLog_rejection_bound hh ht hth
  calc
    _ ≤ _ := herr
    _ ≤ (4/3 : ℝ)*((32*(h : ℝ)^2+1)*B)*(1/(h : ℝ)^12) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hkernel (by norm_num)) hexp
        (Real.exp_pos _).le (by dsimp [B]; positivity)
    _ = (4/3 : ℝ)*B*((32*(h : ℝ)^2+1)/(h : ℝ)^12) := by ring
    _ ≤ kappa := he.le

def SquareRootBalancedFamilies : Prop :=
  ∃ (q : ℕ) (y : ZMod (3 ^ q)) (kappa B K : ℝ) (H : ℕ),
    1≤q ∧ IsUnit y ∧ 0<kappa ∧ 0<B ∧ 0<K ∧ 2≤H ∧
    ∀ h : ℕ,H≤h → ∀ R : ℤ,(R : ZMod (3 ^ q))=y → ∃ V : Finset Word,
      (∀ w ∈ V,w.length=h ∧ Contributes w R ∧ w.beta≤B ∧
        2*(h : ℝ)-K*sqrtLogProfile h≤(w.total : ℝ) ∧
        (w.total : ℝ)≤2*(h : ℝ)+K*sqrtLogProfile h) ∧
      ((V.image Word.total).card : ℝ)≤(2*K+1)*((h : ℝ)+1) ∧
      kappa≤∑ w ∈ V,wordTransport w 0 R (density 0)

theorem squareRoot_balanced_families : SquareRootBalancedFamilies := by
  classical
  obtain ⟨N0,q,y,kappa,hN0,hq,hy,hk,hpositive⟩ := narrowFlexible_positive_cylinder
  obtain ⟨K,hK,hprefix⟩ := narrowPrefixWindow_bound
  let B : ℝ := (2 : ℝ)^(baseBlockLength+1)+(16 : ℝ)^baseBlockLength
  let K' : ℝ := 8*K+24
  have hK' : 0<K' := by dsimp [K']; linarith
  obtain ⟨P,hP⟩ := eventually_atTop.mp (narrowPruning_eventually (show 0<kappa/2 by linarith))
  have hsmall := (sqrtLogProfile_div_rpow_tendsto (r := 1) (by norm_num)).comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_one] at hsmall
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))
  let H := max 2 (max (selectedDepth N0) (max P L))
  refine ⟨q,y,kappa/2,B,K',H,hq,hy,by linarith,by dsimp [B]; positivity,hK',le_max_left _ _,?_⟩
  intro h hh R hRy
  have hh2 : 2≤h := (le_max_left _ _).trans hh
  have hdepth : selectedDepth N0≤h := (le_max_left _ _).trans ((le_max_right _ _).trans hh)
  have hPh : P≤h := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hh))
  have hLh : L≤h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hh))
  obtain ⟨N,t,hN0N,hlen,hkt,htupper⟩ := exists_flexible_selected_depth N0 h hdepth
  have htN : t≤2*blockLength N := by
    have hu := (nextBlockDepth_bounds N).2
    have hb : (0 : ℝ)≤blockLength N := by positivity
    have hR : ((blockLength N+terminalDepth (N+1) : ℕ) : ℝ)≤2*blockLength N := by linarith
    have hNat : blockLength N+terminalDepth (N+1)≤2*blockLength N := by exact_mod_cast hR
    exact htupper.trans hNat
  have hblock : (blockLength N : ℝ)≤8*h := by
    have hk := (terminalDepth_real_bounds N).1
    have htR : (terminalDepth N : ℝ)≤t := by exact_mod_cast hkt
    have hth : (t : ℝ)≤h := by exact_mod_cast (show t≤h by omega)
    linarith
  have hp := (sqrtLogProfile_mono (show (1 : ℝ)≤blockLength N by
    exact_mod_cast (blockLength_ge_200 N).trans' (by norm_num : 1≤200)) hblock).trans
      (sqrtLogProfile_scale_eight (by exact_mod_cast hh2))
  have hpre := (hprefix N).trans (mul_le_mul_of_nonneg_left hp hK.le)
  have hm := (sqrtLogWindow_bounds hh2).2.2
  have hwindow : (narrowPrefixWindow N+sqrtLogWindow h : ℝ)≤K'*sqrtLogProfile h := by
    dsimp [K']; nlinarith
  let S := narrowPrunedPrefixes N t (sqrtLogWindow h)
  let V := S.filter (fun w => Contributes w R)
  have hstats : ∀ w ∈ V,w.length=h ∧ Contributes w R ∧ w.beta≤B ∧
      2*(h : ℝ)-K'*sqrtLogProfile h≤(w.total : ℝ) ∧
      (w.total : ℝ)≤2*(h : ℝ)+K'*sqrtLogProfile h := by
    intro w hw
    obtain ⟨hwS,hc⟩ := Finset.mem_filter.mp hw
    have hwold := narrowPrunedPrefixes_subset N t (sqrtLogWindow h) hwS
    have hwlen := terminalPrunedPrefixes_length hwold
    have hbeta := terminalPrunedPrefixes_beta_bound htN hwold
    have hb := narrowPrunedPrefixes_total_bounds hwS
    rw [← hlen] at hwlen hb
    have hlo : 2*(h : ℝ)≤(w.total : ℝ)+(narrowPrefixWindow N+sqrtLogWindow h : ℝ) := by exact_mod_cast hb.1
    have hhi : (w.total : ℝ)≤2*(h : ℝ)+(narrowPrefixWindow N+sqrtLogWindow h : ℝ) := by exact_mod_cast hb.2
    exact ⟨hwlen,hc,hbeta,by linarith,by linarith⟩
  refine ⟨V,hstats,?_,?_⟩
  · have hc : ((V.image Word.total).card : ℝ)≤2*(narrowPrefixWindow N+sqrtLogWindow h : ℝ)+1 := by
      exact_mod_cast (Finset.card_le_card (Finset.image_subset_image
        (Finset.filter_subset (fun w => Contributes w R) S))).trans (narrowPrunedPrefixes_image_card N t (sqrtLogWindow h))
    have hph : sqrtLogProfile h≤(h : ℝ) := by
      have hp : (0 : ℝ)<h := by exact_mod_cast (show 0<h by omega)
      simpa only [one_mul] using (div_le_iff₀ hp).1 (hL h hLh).le
    have hmul := mul_le_mul_of_nonneg_left hph hK'.le
    have hh0 : (0 : ℝ)≤h := by positivity
    nlinarith
  · have hmass : (∑ w ∈ V,wordTransport w 0 R (density 0))=
        ∑ w ∈ S,wordTransport w 0 R (density 0) := by
      dsimp [V]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hc : Contributes w R
      · simp only [hc,ite_true]
      · simp only [hc,ite_false,wordTransport,if_neg hc]
    rw [hmass]
    have hpos := hpositive N hN0N t hkt htN R hRy
    have herr := hP h hPh N t hlen hkt htN R
    have hlo := (abs_le.mp herr).1
    linarith

end SyracuseReport
