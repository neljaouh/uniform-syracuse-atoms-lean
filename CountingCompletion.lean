import ActualAdmissibleFamilies
import AtomFloorBridge
import CorePositiveApproximants
import CountingTransfer
import FlexibleSelectedDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Choose
import PaperStatements
import SelectedCoreWitness
import SelectedDepthCoverage
import SelectedScheduleAsymptotics
import TerminalBandTransport
import WordBarrier
import WordMassPigeonhole

/-! Flexible selected densities, balanced inverse-word families, and the
signed predecessor-counting theorem. The exact manuscript contracts are
checked by CheckPaper. -/


/-! SelectedCylinderPositivity -/

/-! A positive cylinder persists when the terminal length varies between
successive scales. This is the pointwise input for choosing inverse words
at a prescribed length. -/

namespace SyracuseReport
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

theorem heq_residue_function_int_evaluation {n m : ℕ}
    (f : ZMod (3 ^ n) → ℝ) (g : ZMod (3 ^ m) → ℝ)
    (hnm : n = m) (hfg : HEq f g) (M : ℤ) :
    f (M : ZMod (3 ^ n)) = g (M : ZMod (3 ^ m)) := by
  subst m
  have h := eq_of_heq hfg
  rw [h]

theorem selectedDensity_positive_cylinder :
    ∃ (N0 q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ N0 ∧ 1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ N : ℕ, N0 ≤ N →
        q ≤ selectedDepth N ∧
        ∀ M : ℤ, (M : ZMod (3 ^ q)) = y →
          kappa ≤ selectedDensity N (M : ZMod (3 ^ selectedDepth N)) := by
  obtain ⟨C, W, hC, hmark, hexcess, hs, hactual⟩ := paper_thm_construction
  obtain ⟨N0, q, y, kappa, hN0, hqeq, hq, hy, hkappa, hpositive⟩ :=
    W.positive_approximant_cylinder
  refine ⟨N0, q, y, kappa, hN0, hq, hy, hkappa, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := hN0.trans hN
  have hdepth := (hactual N hN1).1
  have hqN : q ≤ selectedDepth N := by
    rw [hqeq, (hactual N0 hN0).1]
    exact selectedDepth_monotone hN
  refine ⟨hqN, ?_⟩
  intro M hMy
  have hqW : q ≤ W.depth N := by rwa [hdepth]
  have hp := hpositive N hN hqW (M : ZMod (3 ^ W.depth N))
    (by simpa only [residueProjection_intCast] using hMy)
  have heval := heq_residue_function_int_evaluation
    (W.approximate N) (selectedDensity N) hdepth (hactual N hN1).2.1 M
  rwa [heval] at hp

theorem flexibleSelectedDensity_error_le_increment (D : ℝ)
    (hmix : ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
          (2 / 3 : ℝ) * D / (m : ℝ) ^ 6)
    (N t : ℕ) (hkt : terminalDepth N ≤ t) (ht : t ≤ 2 * blockLength N)
    (M : ℤ) :
    |flexibleSelectedDensity N t (M : ZMod (3 ^ (prefixDepth N + t))) -
      selectedDensity N (M : ZMod (3 ^ selectedDepth N))| ≤
      selectedIncrementBound D N := by
  have hc := flexibleSelectedDensity_comparison D hmix N t hkt ht M
  have hrej : 0 ≤ 1 - blockProbability N := sub_nonneg.mpr (blockProbability_le_one N)
  have hK : 0 ≤ selectedKernelConstant N := by
    unfold selectedKernelConstant
    positivity
  refine hc.trans ?_
  unfold selectedIncrementBound
  calc
    selectedKernelConstant N * ((2 / 3 : ℝ) * D / (terminalDepth N : ℝ) ^ 6) =
        (2 / 3 : ℝ) * selectedKernelConstant N * (D / (terminalDepth N : ℝ) ^ 6) := by ring
    _ ≤ (2 / 3 : ℝ) * selectedKernelConstant N *
        (D / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hrej) (by positivity)

theorem flexibleSelectedDensity_positive_cylinder :
    ∃ (N0 q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ N0 ∧ 1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ N : ℕ, N0 ≤ N →
        q ≤ selectedDepth N ∧
        ∀ t : ℕ, terminalDepth N ≤ t → t ≤ 2 * blockLength N →
          ∀ M : ℤ, (M : ZMod (3 ^ q)) = y →
            kappa ≤ flexibleSelectedDensity N t
              (M : ZMod (3 ^ (prefixDepth N + t))) := by
  obtain ⟨K, q, y, kappa, hK, hq, hy, hkappa, hpositive⟩ :=
    selectedDensity_positive_cylinder
  obtain ⟨D, hD, hmix⟩ := paper_thm_mixing 6 (by norm_num)
  have hs := summable_selectedIncrementBound hD blockProbability_le_one block_rejection_bound
  have hev : ∀ᶠ N : ℕ in atTop, selectedIncrementBound D N < kappa / 2 :=
    (tendsto_order.mp hs.tendsto_atTop_zero).2 _ (by linarith)
  obtain ⟨L, hL⟩ := eventually_atTop.mp hev
  refine ⟨max K L, q, y, kappa / 2, hK.trans (le_max_left _ _),
    hq, hy, by linarith, ?_⟩
  intro N hN
  have hKN : K ≤ N := (le_max_left K L).trans hN
  have hLN : L ≤ N := (le_max_right K L).trans hN
  obtain ⟨hqN, hposN⟩ := hpositive N hKN
  refine ⟨hqN, ?_⟩
  intro t hkt ht M hMy
  have hp := hposN M hMy
  have he := flexibleSelectedDensity_error_le_increment D hmix N t hkt ht M
  have hlower := (abs_le.mp he).1
  have hsmall := hL N hLN
  linarith

end SyracuseReport

/-! TerminalPruningAsymptotics -/

/-! Uniform terminal pruning at a window proportional to the full length. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def terminalWindow (delta : ℝ) (h : ℕ) : ℕ :=
  Nat.ceil (delta * (h : ℝ) / 10000)

theorem terminalWindow_bounds {delta : ℝ} (hdelta : 0 < delta)
    (h : ℕ) (hlarge : 10000 ≤ delta * (h : ℝ)) :
    0 < terminalWindow delta h ∧
    delta * (h : ℝ) / 10000 ≤ terminalWindow delta h ∧
    (terminalWindow delta h : ℝ) ≤ delta * (h : ℝ) / 5000 := by
  have hlo : delta * (h : ℝ) / 10000 ≤ (terminalWindow delta h : ℝ) := Nat.le_ceil _
  have hhi : (terminalWindow delta h : ℝ) ≤ 2 * (delta * (h : ℝ) / 10000) := by
    apply Nat.ceil_le_two_mul
    linarith
  refine ⟨?_, hlo, by linarith⟩
  have hp : (0 : ℝ) < terminalWindow delta h := by linarith
  exact_mod_cast hp

theorem terminalWindow_small {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 100) (N t h : ℕ)
    (hlen : h = prefixDepth N + t) (hkt : terminalDepth N ≤ t)
    (htN : t ≤ 2 * blockLength N) (hlarge : 10000 ≤ delta * (h : ℝ)) :
    (terminalWindow delta h : ℝ) ≤ (3 / 2 : ℝ) * t := by
  have hw := (terminalWindow_bounds hdelta h hlarge).2.2
  have hlenR : (h : ℝ) ≤ 1616 * t := by
    have hl : h ≤ 1616 * t := by
      rw [hlen]
      exact flexible_length_le_terminal N t hkt htN
    exact_mod_cast hl
  have hdh := mul_le_mul_of_nonneg_right hsmall (show (0 : ℝ) ≤ h by positivity)
  linarith

theorem terminalWindow_exponent_lower {delta : ℝ} (hdelta : 0 < delta)
    (h t : ℕ) (ht : 0 < t) (hth : t ≤ h) (hlarge : 10000 ≤ delta * (h : ℝ)) :
    (delta ^ 2 / (12 * 10000 ^ 2)) * (h : ℝ) ≤
      (terminalWindow delta h : ℝ) ^ 2 / (12 * (t : ℝ)) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hhpos : (0 : ℝ) < h := by exact_mod_cast ht.trans_le hth
  have hthR : (t : ℝ) ≤ h := by exact_mod_cast hth
  have hm := (terminalWindow_bounds hdelta h hlarge).2.1
  calc
    (delta ^ 2 / (12 * 10000 ^ 2)) * (h : ℝ) =
        (delta * (h : ℝ) / 10000) ^ 2 / (12 * (h : ℝ)) := by
          field_simp [hhpos.ne']
    _ ≤ (terminalWindow delta h : ℝ) ^ 2 / (12 * (h : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hm 2
    _ ≤ (terminalWindow delta h : ℝ) ^ 2 / (12 * (t : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hthR (by norm_num))

theorem terminalPruning_uniform_error_eventually {delta kappa : ℝ}
    (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 100) (hkappa : 0 < kappa) :
    ∀ᶠ h : ℕ in atTop, ∀ N t : ℕ,
      h = prefixDepth N + t → terminalDepth N ≤ t → t ≤ 2 * blockLength N →
      ∀ M : ℤ,
        |(∑ w ∈ terminalPrunedPrefixes N t (terminalWindow delta h),
            wordTransport w 0 M (density 0)) -
          familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
            (M : ZMod (3 ^ (prefixDepth N + t)))| ≤ kappa := by
  let a : ℝ := delta ^ 2 / (12 * 10000 ^ 2)
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have henv : Tendsto (fun h : ℕ =>
      (4 / 3 : ℝ) * B * ((32 * (h : ℝ) ^ 2 + 1) * Real.exp (-a * h)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((quadratic_pruning_envelope_tendsto ha).comp tendsto_natCast_atTop_atTop).const_mul
        ((4 / 3 : ℝ) * B)
  have henvsmall := henv.eventually (eventually_lt_nhds hkappa)
  have hlarge : ∀ᶠ h : ℕ in atTop, 10000 ≤ delta * (h : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (10000 / delta))] with h hh
    have hbound : (10000 / delta : ℝ) ≤ h :=
      (Nat.le_ceil _).trans (by exact_mod_cast hh)
    exact (div_le_iff₀ hdelta).mp hbound |>.trans_eq (mul_comm _ _)
  filter_upwards [henvsmall, hlarge] with h he hlarge
  intro N t hlen hkt htN M
  have ht : 0 < t := lt_of_lt_of_le (terminalDepth_pos N) hkt
  have hth : t ≤ h := by omega
  have hm := (terminalWindow_bounds hdelta h hlarge).1
  have hmsmall := terminalWindow_small hdelta hsmall N t h hlen hkt htN hlarge
  have herror := terminalPruning_exponential_error N t (terminalWindow delta h)
    ht hm htN hmsmall M
  have hkernel := selectedKernelConstant_quadratic_length_bound N t hkt
  rw [← hlen] at hkernel
  have hexp : Real.exp (-((terminalWindow delta h : ℝ) ^ 2) / (12 * (t : ℝ))) ≤
      Real.exp (-a * h) := by
    apply Real.exp_le_exp.mpr
    have hl := terminalWindow_exponent_lower hdelta h t ht hth hlarge
    change a * (h : ℝ) ≤ _ at hl
    simpa only [neg_div, neg_mul] using (neg_le_neg hl)
  calc
    _ ≤ (4 / 3 : ℝ) * selectedKernelConstant N *
        Real.exp (-((terminalWindow delta h : ℝ) ^ 2) / (12 * (t : ℝ))) := herror
    _ ≤ (4 / 3 : ℝ) * ((32 * (h : ℝ) ^ 2 + 1) * B) * Real.exp (-a * h) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hkernel (by norm_num)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = (4 / 3 : ℝ) * B * ((32 * (h : ℝ) ^ 2 + 1) * Real.exp (-a * h)) := by ring
    _ ≤ kappa := he.le

end SyracuseReport

/-! ActualBalancedConstruction -/

/-! Positive transport mass for the actual balanced families at every large
length. This connects the selected-density construction to word counting. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem actual_balanced_cylinder_families : ActualBalancedCylinderFamilies := by
  obtain ⟨N0, q, y, kappa, hN0, hq, hy, hkappa, hpositive⟩ :=
    flexibleSelectedDensity_positive_cylinder
  refine ⟨q, y, kappa / 2, hq, hy, by linarith, ?_⟩
  intro delta hdelta hsmall
  have hwindowevent : ∀ᶠ N : ℕ in atTop,
      (prefixWindow N : ℝ) / (selectedDepth N : ℝ) < delta / 2 :=
    (tendsto_order.mp prefixWindow_selectedDepth_ratio_tendsto).2 _ (by linarith)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hwindowevent
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (terminalPruning_uniform_error_eventually hdelta hsmall
      (show 0 < kappa / 2 by linarith))
  have hdtop : Tendsto (fun h : ℕ => delta * (h : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hdelta
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (hdtop.eventually (eventually_ge_atTop (10000 : ℝ)))
  let J := max N0 K
  let H := max (selectedDepth J) (max P L)
  refine ⟨H, ?_⟩
  intro h hh R hRy
  have hdepthh : selectedDepth J ≤ h := (le_max_left _ _).trans hh
  have hPh : P ≤ h := (le_max_left P L).trans ((le_max_right _ _).trans hh)
  have hLh : L ≤ h := (le_max_right P L).trans ((le_max_right _ _).trans hh)
  obtain ⟨N, t, hJN, hlen, hkt, htupper⟩ := exists_flexible_selected_depth J h hdepthh
  have hN0N : N0 ≤ N := (le_max_left _ _).trans hJN
  have hKN : K ≤ N := (le_max_right _ _).trans hJN
  have htN : t ≤ 2 * blockLength N := by
    have hr := (nextBlockDepth_bounds N).2
    have hnonneg : (0 : ℝ) ≤ blockLength N := by positivity
    have hupperR : ((blockLength N + terminalDepth (N + 1) : ℕ) : ℝ) ≤
        2 * blockLength N := by linarith
    have hu : blockLength N + terminalDepth (N + 1) ≤ 2 * blockLength N := by
      exact_mod_cast hupperR
    exact htupper.trans hu
  have hlarge : 10000 ≤ delta * (h : ℝ) := hL h hLh
  have hwindow : (prefixWindow N : ℝ) ≤ (delta / 2) * (h : ℝ) := by
    have hw := (hK N hKN).le
    have hdpos : (0 : ℝ) < selectedDepth N := by exact_mod_cast selectedDepth_positive N
    have hsmallDepth : selectedDepth N ≤ h := by unfold selectedDepth; omega
    have hsmallDepthR : (selectedDepth N : ℝ) ≤ h := by exact_mod_cast hsmallDepth
    exact ((div_le_iff₀ hdpos).mp hw).trans
      (mul_le_mul_of_nonneg_left hsmallDepthR (by positivity))
  have hm := (terminalWindow_bounds hdelta h hlarge).2.2
  refine ⟨N, t, terminalWindow delta h, hlen, htN, by linarith, ?_⟩
  have hpos := (hpositive N hN0N).2 t hkt htN R hRy
  have herr := hP h hPh N t hlen hkt htN R
  change kappa ≤ familyTransport (selectedPrefixes N) (prefixDepth N) t (density t)
    (R : ZMod (3 ^ (prefixDepth N + t))) at hpos
  have hlower := (abs_le.mp herr).1
  linarith

end SyracuseReport

/-! WordOffsetBarrier -/

/-! A bounded affine offset forces every inverse-prefix barrier. -/

namespace SyracuseReport

theorem inverse_prefix_term_le_beta (w : Word) :
    ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
      (3 : ℝ) ^ (i - 1) / (2 : ℝ) ^ inversePrefixTotal w i ≤ w.beta := by
  induction w with
  | nil => intro i hi hlen; simp only [Word.length_nil] at hlen; omega
  | snoc w a ih =>
      intro i hi hlen
      by_cases hprev : i ≤ w.length
      · rw [inversePrefixTotal_snoc_le w a i hprev]
        apply (ih i hi hprev).trans
        rw [Word.beta_snoc]
        have hp : 0 ≤ (3 : ℝ) ^ w.length / (2 : ℝ) ^ (Word.snoc w a).total :=
          by positivity
        linarith
      · have heq : i = (Word.snoc w a).length := by
          simp only [Word.length_snoc] at hlen ⊢
          omega
        rw [heq, inversePrefixTotal_full, Word.beta_snoc]
        simp only [Word.length_snoc, Nat.add_sub_cancel]
        have hp := w.beta_nonneg
        linarith

theorem inverse_prefix_barrier_of_beta (w : Word) (B D : ℝ)
    (hB : 0 < B) (hbeta : w.beta ≤ B)
    (hscale : Real.log (3 * B) ≤ D * Real.log 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
      -D ≤ (inversePrefixTotal w i : ℝ) -
        (i : ℝ) * (Real.log 3 / Real.log 2) := by
  intro i hi hlen
  have hterm := (inverse_prefix_term_le_beta w i hi hlen).trans hbeta
  have hlog := Real.log_le_log (by positivity) hterm
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_pow] at hlog
  have hiR : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi] <;> norm_num
  rw [hiR] at hlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscale' := hscale
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hB.ne'] at hscale'
  apply (mul_le_mul_iff_right₀ hlog2).mp
  have hcancel : Real.log 2 * ((i : ℝ) * (Real.log 3 / Real.log 2)) =
      (i : ℝ) * Real.log 3 := by
    field_simp [hlog2.ne'] <;> ring
  rw [mul_sub, hcancel]
  nlinarith

end SyracuseReport

/-! BalancedWordBudgets -/
set_option backward.isDefEq.respectTransparency false

/-! A rounded word length and a narrow terminal valuation band satisfy
the exact exponential budgets in the admissible-word contract. -/

namespace SyracuseReport

set_option maxHeartbeats 2000000 in
theorem rounded_balanced_word_budget (eta x : ℝ) (n L : ℕ)
    (heta : 0 < eta) (hsmall : eta ≤ 1 / 100)
    (hbase : 400 ≤ eta ^ 2 * x)
    (hn : 1 ≤ n) (hnlo : x ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ x + 1)
    (hLlo : 2 * ((n - 1 : ℕ) : ℝ) - (eta ^ 2 / 100) * ((n - 1 : ℕ) : ℝ) ≤ (L : ℝ))
    (hLhi : (L : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) +
      (eta ^ 2 / 100) * ((n - 1 : ℕ) : ℝ)) :
    Real.exp ((1 - eta ^ 2) * (x * Real.log (4 / 3 : ℝ))) ≤
        (3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L ∧
    (3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L ≤
        Real.exp ((1 + eta ^ 2) * (x * Real.log (4 / 3 : ℝ))) ∧
    (2 - eta ^ 2) * (n : ℝ) ≤ (L : ℝ) ∧
    (L : ℝ) ≤ (2 + eta ^ 2) * (n : ℝ) := by
  have hquad : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hquad1 : eta ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self heta.le hsmall]
  have hxpos : 0 < x := by nlinarith
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn] <;> norm_num
  rw [hpred] at hLlo hLhi
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlogAlphaLo : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at hh ⊢
    exact hh
  have hlogAlphaHi : Real.log (4 / 3 : ℝ) ≤ 1 / 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at hh ⊢
    exact hh
  have hlogAlpha : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] <;> norm_num
  have hscale : (eta ^ 2 / 100) * (n : ℝ) ≤ (eta ^ 2 / 100) * (x + 1) :=
    mul_le_mul_of_nonneg_left hnhi (by positivity)
  have herror : 2 + (eta ^ 2 / 100) * (n : ℝ) ≤ eta ^ 2 * x / 4 := by
    nlinarith only [hbase, hscale, hquad1]
  have hbudgetError : 2 + (eta ^ 2 / 100) * (n : ℝ) ≤
      eta ^ 2 * (x * Real.log (4 / 3 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlogAlphaLo
      (show 0 ≤ eta ^ 2 * x by positivity)
    nlinarith only [herror, hh]
  have hLlower : 2 * (n : ℝ) - (2 + (eta ^ 2 / 100) * (n : ℝ)) ≤ (L : ℝ) := by
    nlinarith only [hLlo, hquad]
  have hLupper : (L : ℝ) ≤ 2 * (n : ℝ) + (eta ^ 2 / 100) * (n : ℝ) := by
    nlinarith only [hLhi, hquad]
  have hLlogLower := mul_le_mul_of_nonneg_right hLlower hlog2pos.le
  have hLlogUpper := mul_le_mul_of_nonneg_right hLupper hlog2pos.le
  have herrorLog := mul_le_mul_of_nonneg_left hlog2
    (show 0 ≤ 2 + (eta ^ 2 / 100) * (n : ℝ) by positivity)
  have hdeltaLog := mul_le_mul_of_nonneg_left hlog2
    (show 0 ≤ (eta ^ 2 / 100) * (n : ℝ) by positivity)
  have hroundLower := mul_le_mul_of_nonneg_right hnlo
    ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hlogAlphaLo)
  have hroundUpper := mul_le_mul_of_nonneg_right hnhi
    ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hlogAlphaLo)
  have hlogBudget : Real.log ((3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L) =
      -(n : ℝ) * Real.log 3 + (L : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_pow]
    simp only [Int.cast_neg, Int.cast_natCast]
  have hbudgetLower : (1 - eta ^ 2) * (x * Real.log (4 / 3 : ℝ)) ≤
      Real.log ((3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L) := by
    rw [hlogBudget]
    rw [hlogAlpha] at hroundLower hbudgetError ⊢
    nlinarith only [hLlogLower, herrorLog, hbudgetError, hroundLower]
  have hbudgetUpper : Real.log ((3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L) ≤
      (1 + eta ^ 2) * (x * Real.log (4 / 3 : ℝ)) := by
    rw [hlogBudget]
    rw [hlogAlpha] at hroundUpper hbudgetError hlogAlphaHi ⊢
    nlinarith only [hLlogUpper, hdeltaLog, hroundUpper, hbudgetError, hlogAlphaHi]
  have hnearError : 2 + (eta ^ 2 / 100) * (n : ℝ) ≤ eta ^ 2 * (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hnlo hquad.le
    nlinarith only [hbase, hh]
  refine ⟨(Real.le_log_iff_exp_le (by positivity)).mp hbudgetLower,
    (Real.log_le_iff_le_exp (by positivity)).mp hbudgetUpper, ?_, ?_⟩
  · nlinarith only [hLlower, hnearError]
  · nlinarith only [hLupper, mul_nonneg hquad.le hnR]

end SyracuseReport

/-! CountingPolynomialLoss -/

/-! The finite valuation pigeonhole loss is absorbed by the small
exponential loss allowed in the admissible-word statement. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem tendsto_affine_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (2 * t + 1) * Real.exp (-a * t)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun t : ℝ => a * t) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hlin := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hconst := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hscale)
  have hsum : Tendsto (fun t : ℝ =>
      (2 / a) * ((a * t) * Real.exp (-(a * t))) + Real.exp (-(a * t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, mul_zero, zero_add] using
      (hlin.const_mul (2 / a)).add hconst
  convert hsum using 1
  funext t
  simp only [neg_mul]
  field_simp [ha.ne'] <;> ring

theorem eventually_valuation_pigeonhole_loss (a kappa : ℝ)
    (ha : 0 < a) (hkappa : 0 < kappa) :
    ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) + 1) * Real.exp (-a * (n : ℝ)) ≤ kappa := by
  exact ((tendsto_affine_mul_exp_neg a ha).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds hkappa)

end SyracuseReport

/-! GeometricCutoffs -/
set_option backward.isDefEq.respectTransparency false

/-! Passing from geometrically spaced exponential cutoffs to every large
real cutoff. The strict exponent margin is stated explicitly. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem oddRootPredecessorCount_mono (R : ℤ) :
    Monotone (oddRootPredecessorCount R) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro m hm
  simp only [oddRootPredecessorCount, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  exact ⟨⟨(Int.ceil_mono (neg_le_neg hxy)).trans hm.1.1,
    hm.1.2.trans (Int.floor_mono hxy)⟩, hm.2⟩

theorem lower_at_every_cutoff_of_geometric_exponentials
    (F : ℝ → ℝ) (hF : Monotone F)
    (s r a c gamma : ℝ) (hs : 0 < s) (hr : 1 < r)
    (hc : 0 < c) (hgamma : 0 ≤ gamma) (hmargin : gamma * c * r ≤ a)
    (J : ℕ)
    (hfamily : ∀ j : ℕ, J ≤ j →
      Real.exp (a * (s * r ^ j)) ≤ F (Real.exp (c * (s * r ^ j)))) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x → x ^ gamma ≤ F x := by
  let X : ℕ → ℝ := fun j => Real.exp (c * (s * r ^ j))
  have hXmono : Monotone X := by
    intro i j hij
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le hij) hs.le) hc.le
  have hXtop : Tendsto X atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop hs).const_mul_atTop hc)
  refine ⟨max 2 (X J), le_max_left _ _, ?_⟩
  intro x hx
  have hxX : X J ≤ x := (le_max_right _ _).trans hx
  have hex : ∃ k : ℕ, x < X k := by
    obtain ⟨k, hk⟩ := (eventually_atTop.1 (hXtop.eventually (eventually_gt_atTop x)))
    exact ⟨k, hk k le_rfl⟩
  let k := Nat.find hex
  have hk : x < X k := Nat.find_spec hex
  have hJk : J < k := by
    by_contra h
    have hkJ : k ≤ J := by omega
    exact (not_lt_of_ge (hXmono hkJ |>.trans hxX)) hk
  let j := k - 1
  have hjJ : J ≤ j := by dsimp [j]; omega
  have hjk : j + 1 = k := by dsimp [j]; omega
  have hj : X j ≤ x := by
    apply le_of_not_gt
    exact Nat.find_min hex (by dsimp [j, k]; omega)
  have hstep : x < Real.exp (c * (s * r ^ (j + 1))) := by
    simpa only [hjk] using hk
  have hxpos : 0 < x := by
    have := le_max_left (2 : ℝ) (X J)
    linarith
  have hpow : x ^ gamma ≤ (Real.exp (c * (s * r ^ (j + 1)))) ^ gamma :=
    Real.rpow_le_rpow hxpos.le hstep.le hgamma
  rw [← Real.exp_mul] at hpow
  have hscaled : (c * (s * r ^ (j + 1))) * gamma ≤ a * (s * r ^ j) := by
    have htau : 0 ≤ s * r ^ j := by positivity
    have hh := mul_le_mul_of_nonneg_right hmargin htau
    rw [pow_succ]
    nlinarith
  exact hpow.trans ((Real.exp_le_exp.mpr hscaled).trans
    ((hfamily j hjJ).trans (hF hj)))

theorem eventually_absorb_affine_factor (B c delta : ℝ) (hB : 0 < B)
    (hdelta : 0 < delta) :
    ∀ᶠ t : ℝ in atTop,
      B * (1 + t) * Real.exp (c * t) ≤ Real.exp ((c + delta) * t) := by
  have hlog : Tendsto (fun t : ℝ => Real.log (1 + t) / t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    convert hh using 1
    funext t
    simp only [Function.comp_apply, id_eq, pow_one, one_mul]
    congr 2 <;> ring
  have hsmall : Tendsto (fun t : ℝ =>
      Real.log B / t + Real.log (1 + t) / t) atTop (𝓝 (0 + 0)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add hlog
  have hevent : ∀ᶠ t : ℝ in atTop,
      Real.log B / t + Real.log (1 + t) / t < delta :=
    hsmall.eventually (eventually_lt_nhds (by simpa using hdelta))
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hpoly : Real.log B + Real.log (1 + t) ≤ delta * t := by
    rw [← add_div] at ht
    exact ((div_lt_iff₀ htpos).mp ht).le
  have hBexp : B = Real.exp (Real.log B) := (Real.exp_log hB).symm
  have htexp : 1 + t = Real.exp (Real.log (1 + t)) :=
    (Real.exp_log (by linarith)).symm
  rw [hBexp, htexp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end SyracuseReport

/-! AdmissibleWordReduction -/

/-! The quantitative admissible-word contract implies the manuscript's
signed good-root estimate. The admissible-word contract is an explicit
premise; its construction is a separate obligation. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem log_four_thirds_lower : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  norm_num at h ⊢
  exact h

theorem log_four_thirds_eq : Real.log (4 / 3 : ℝ) =
    2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] <;> norm_num

theorem budget_log (n L : ℕ) :
    Real.log ((3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L) =
      -(n : ℝ) * Real.log 3 + (L : ℝ) * Real.log 2 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_pow]
  simp only [Int.cast_neg, Int.cast_natCast]

theorem admissible_length_and_count (eta tau : ℝ) (n L card : ℕ)
    (heta : 0 < eta) (hsmall : eta ≤ 1 / 100) (htau : 0 ≤ tau)
    (hbudgetLo : Real.exp ((1 - eta ^ 2) * tau) ≤
      (3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L)
    (hbudgetHi : (3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L ≤
      Real.exp ((1 + eta ^ 2) * tau))
    (hL : (2 - eta ^ 2) * (n : ℝ) ≤ (L : ℝ))
    (hcard : Real.rpow 3 (-(n : ℝ) - eta ^ 4 * (n : ℝ)) *
      (2 : ℝ) ^ L ≤ (card : ℝ)) :
    (n : ℝ) ≤ 6 * tau ∧ Real.exp ((1 - eta) * tau) ≤ (card : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog3pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hquad : eta ^ 2 ≤ eta / 100 := by
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr hsmall)]
  have hquad1 : eta ^ 2 ≤ 1 / 10000 := by
    nlinarith [mul_self_le_mul_self heta.le hsmall]
  have hfour : eta ^ 4 ≤ eta ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg eta)
      (show 0 ≤ 1 - eta ^ 2 by nlinarith)]
  have hdeficit : eta ^ 2 + 12 * eta ^ 4 ≤ eta := by
    nlinarith only [hquad, hfour, heta.le]
  have ha : (1 / 5 : ℝ) ≤ (2 - eta ^ 2) * Real.log 2 - Real.log 3 := by
    have hh := log_four_thirds_lower
    rw [log_four_thirds_eq] at hh
    have hm := mul_le_mul_of_nonneg_left hlog2 (sq_nonneg eta)
    nlinarith only [hh, hm, hquad1]
  have hupper := Real.log_le_log (by positivity) hbudgetHi
  rw [budget_log, Real.log_exp] at hupper
  have hlower := Real.log_le_log (Real.exp_pos _) hbudgetLo
  rw [Real.log_exp, budget_log] at hlower
  have hLlog := mul_le_mul_of_nonneg_right hL hlog2pos.le
  have hn : (0 : ℝ) ≤ n := by positivity
  have han := mul_le_mul_of_nonneg_right ha hn
  have hbudgetTau := mul_le_mul_of_nonneg_right
    (show 1 + eta ^ 2 ≤ (6 / 5 : ℝ) by nlinarith) htau
  have hnBound : (n : ℝ) ≤ 6 * tau := by
    nlinarith only [hupper, hLlog, han, hbudgetTau]
  refine ⟨hnBound, ?_⟩
  have hrawpos : 0 < Real.rpow 3 (-(n : ℝ) - eta ^ 4 * (n : ℝ)) *
      (2 : ℝ) ^ L := by
    rw [Real.rpow_eq_pow]
    positivity
  apply (Real.le_log_iff_exp_le ((hrawpos.trans_le hcard))).mp
  have hrawlog := Real.log_le_log hrawpos hcard
  rw [Real.rpow_eq_pow] at hrawlog
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0 : ℝ) < 3), Real.log_pow] at hrawlog
  have herror : eta ^ 4 * (n : ℝ) * Real.log 3 ≤ 12 * eta ^ 4 * tau := by
    calc
      eta ^ 4 * (n : ℝ) * Real.log 3 ≤ eta ^ 4 * (6 * tau) * 2 := by gcongr
      _ = 12 * eta ^ 4 * tau := by ring
  have hdeficitTau := mul_le_mul_of_nonneg_right hdeficit htau
  nlinarith only [hlower, hrawlog, herror, hdeficitTau]

theorem word_budget_scale (n L : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ L / (3 : ℝ) ^ (n - 1) =
      3 * ((3 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ L) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, zpow_neg, zpow_natCast,
    pow_succ]
  field_simp

theorem good_roots_of_admissible_words (hwords : PaperStatements.admissible_words) :
    PaperStatements.lem_good_roots := by
  intro hatom gamma hgamma
  obtain ⟨eta0, heta0, _, hinput⟩ := hwords hatom
  let g : ℝ := max gamma 0
  have hg0 : 0 ≤ g := le_max_right _ _
  have hggamma : gamma ≤ g := le_max_left _ _
  have hg1 : g < 1 := max_lt hgamma (by norm_num)
  have hgap0 : 0 < 1 - g := sub_pos.mpr hg1
  let eta : ℝ := min eta0 (min (1 / 100) ((1 - g) / 20)) / 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetamin : eta < min eta0 (min (1 / 100) ((1 - g) / 20)) := by
    dsimp [eta]
    have hp : 0 < min eta0 (min (1 / 100 : ℝ) ((1 - g) / 20)) := by positivity
    linarith
  have heta0' : eta < eta0 := hetamin.trans_le (min_le_left _ _)
  have hsmall : eta ≤ 1 / 100 :=
    (hetamin.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hgap : 20 * eta < 1 - g := by
    have hh := hetamin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have heta1 : eta ≤ 1 := by linarith
  have hquad : eta ^ 2 ≤ eta := by
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr heta1)]
  have hmargin : g * (1 + 2 * eta) * (1 + eta) ≤ 1 - eta := by
    have hm1 := mul_le_mul_of_nonneg_right hg1.le heta.le
    have hm2 := mul_le_mul_of_nonneg_right hg1.le (sq_nonneg eta)
    nlinarith
  obtain ⟨n0, b, hn0, hb, hroots⟩ := hinput eta heta heta0'
  refine ⟨n0, b, by omega, hb, ?_⟩
  intro R hR hRb
  obtain ⟨n, L, V, hfamilies⟩ := hroots R hRb
  let tau : ℕ → ℝ := fun j => (1 + eta) ^ j * (n0 : ℝ) * Real.log (4 / 3 : ℝ)
  let K : ℝ := (2 : ℝ) ^ (eta ^ 5 * (n0 : ℝ)) / 3
  let B : ℝ := 3 * (|(R : ℝ)| + 6 * K + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have htau : ∀ j, 0 < tau j := by
    intro j
    dsimp [tau]
    have hlog : 0 < Real.log (4 / 3 : ℝ) :=
      (by norm_num : (0 : ℝ) < 1 / 4).trans_le log_four_thirds_lower
    positivity
  have hcounts : ∀ j, Real.exp ((1 - eta) * tau j) ≤ ((V j).card : ℝ) := by
    intro j
    obtain ⟨_, _, _, hlo, hhi, hL, _, hcard, _⟩ := hfamilies j
    exact (admissible_length_and_count eta (tau j) (n j) (L j) (V j).card
      heta hsmall (htau j).le hlo hhi hL hcard).2
  have hsize : ∀ j, ∀ w ∈ V j, |(inverseInteger w R : ℝ)| ≤
      B * (1 + tau j) * Real.exp ((1 + eta ^ 2) * tau j) := by
    intro j w hw
    obtain ⟨hn, hstats, hadm, hlo, hhi, hL, _, hcard, hbarrier⟩ := hfamilies j
    have hnBound := (admissible_length_and_count eta (tau j) (n j) (L j)
      (V j).card heta hsmall (htau j).le hlo hhi hL hcard).1
    have hsource := inverse_source_size_from_barrier w R (eta ^ 5 * (n0 : ℝ))
      (hadm w hw) (by simpa only [neg_mul] using hbarrier w hw)
    have hwlen := (hstats w hw).1
    have hwtotal := (hstats w hw).2
    rw [hwlen, hwtotal, word_budget_scale (n j) (L j) hn] at hsource
    have hlen : ((n j - 1 : ℕ) : ℝ) ≤ 6 * tau j := by
      have hsub : n j - 1 ≤ n j := Nat.sub_le _ _
      have hsubR : ((n j - 1 : ℕ) : ℝ) ≤ (n j : ℝ) := by exact_mod_cast hsub
      exact hsubR.trans hnBound
    have hsource' : |(inverseInteger w R : ℝ)| ≤
        3 * Real.exp ((1 + eta ^ 2) * tau j) * (|(R : ℝ)| + K * (6 * tau j)) := by
      apply hsource.trans
      change 3 * ((3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L j) *
        (|(R : ℝ)| + K * ((n j - 1 : ℕ) : ℝ)) ≤ _
      gcongr
    apply hsource'.trans
    have hfactor : 3 * (|(R : ℝ)| + K * (6 * tau j)) ≤ B * (1 + tau j) := by
      dsimp [B]
      nlinarith only [hK.le, (htau j).le,
        mul_nonneg (abs_nonneg (R : ℝ)) (htau j).le]
    have he := mul_le_mul_of_nonneg_right hfactor
      (Real.exp_pos ((1 + eta ^ 2) * tau j)).le
    nlinarith
  have htauTop : Tendsto tau atTop atTop := by
    have hs : 0 < (n0 : ℝ) * Real.log (4 / 3 : ℝ) := by
      have hlog : 0 < Real.log (4 / 3 : ℝ) :=
        (by norm_num : (0 : ℝ) < 1 / 4).trans_le log_four_thirds_lower
      positivity
    convert (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1 + eta)).const_mul_atTop hs using 1
    funext j
    dsimp [tau]
    ring
  have habsorb := htauTop.eventually
    (eventually_absorb_affine_factor B (1 + eta ^ 2) eta hB heta)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp habsorb
  have hfamily : ∀ j, J ≤ j →
      Real.exp ((1 - eta) * tau j) ≤
        (oddRootPredecessorCount R (Real.exp ((1 + 2 * eta) * tau j)) : ℝ) := by
    intro j hj
    have hcontrib : ∀ w ∈ V j, Contributes w R := (hfamilies j).2.2.1
    have hstats : ∀ w ∈ V j, w.length = n j - 1 ∧ w.total = L j :=
      (hfamilies j).2.1
    have hfinalSize : ∀ w ∈ V j, |(inverseInteger w R : ℝ)| ≤
        Real.exp ((1 + 2 * eta) * tau j) := by
      intro w hw
      have hquadTau := mul_le_mul_of_nonneg_right hquad (htau j).le
      exact (hsize j w hw).trans
        ((hJ j hj).trans (Real.exp_le_exp.mpr (by nlinarith)))
    have hcard := word_family_le_oddRootPredecessorCount (V j) R hR
      (n j - 1) (L j) (Real.exp ((1 + 2 * eta) * tau j)) hstats hcontrib hfinalSize
    exact (hcounts j).trans (by exact_mod_cast hcard)
  have hs : 0 < (n0 : ℝ) * Real.log (4 / 3 : ℝ) := by
    have hlog : 0 < Real.log (4 / 3 : ℝ) :=
      (by norm_num : (0 : ℝ) < 1 / 4).trans_le log_four_thirds_lower
    positivity
  obtain ⟨x0, hx0, hcutoffs⟩ := lower_at_every_cutoff_of_geometric_exponentials
    (fun x => (oddRootPredecessorCount R x : ℝ))
    (by
      intro x y hxy
      change (oddRootPredecessorCount R x : ℝ) ≤ (oddRootPredecessorCount R y : ℝ)
      exact_mod_cast oddRootPredecessorCount_mono R hxy)
    ((n0 : ℝ) * Real.log (4 / 3 : ℝ)) (1 + eta) (1 - eta) (1 + 2 * eta) g
    hs (by linarith) (by linarith) hg0 hmargin J (by
      intro j hj
      simpa only [tau, mul_assoc, mul_comm, mul_left_comm] using hfamily j hj)
  refine ⟨x0, hx0, ?_⟩
  intro x hx
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith) hggamma).trans (hcutoffs x hx)

end SyracuseReport

/-! AdmissibleWordsAssembly -/
set_option backward.isDefEq.respectTransparency false

/-! Assembly of the exact admissible-word input from the actual positive
balanced cylinder families. The single premise is an explicitly stated
construction target for the actual selected families; it must itself be
proved before this assembly can close the paper's admissible-word endpoint. -/

namespace SyracuseReport
open Filter
open scoped BigOperators Topology

set_option maxHeartbeats 2000000 in
theorem admissible_words_of_actual_balanced_families
    (hactual : ActualBalancedCylinderFamilies) : PaperStatements.admissible_words := by
  classical
  intro _hatom
  obtain ⟨q, b, kappa, B, hq, hb, hkappa, hB, hfamilies⟩ :=
    balanced_word_families_of_actual hactual
  refine ⟨1 / 100, by norm_num, by norm_num, ?_⟩
  intro eta heta hsmall
  have hsmall' : eta ≤ 1 / 100 := hsmall.le
  have hquad : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hquad1 : eta ^ 2 ≤ 1 := by
    nlinarith only [mul_self_le_mul_self heta.le hsmall']
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let delta : ℝ := eta ^ 2 / 100
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaSmall : delta ≤ 1 / 100 := by
    dsimp [delta]
    nlinarith only [hquad1]
  obtain ⟨H, hH⟩ := hfamilies delta hdelta hdeltaSmall
  let a : ℝ := eta ^ 4 * Real.log 3
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_valuation_pigeonhole_loss a ((9 / 2 : ℝ) * kappa) ha (by positivity))
  obtain ⟨D, hD⟩ := exists_nat_gt
    (max (400 / eta ^ 2) (Real.log (3 * B) / (eta ^ 5 * Real.log 2)))
  let n0 : ℕ := max 2 (max (q + 1) (max (H + 1) (max K D)))
  have hn02 : 2 ≤ n0 := le_max_left _ _
  have hqn0 : q + 1 ≤ n0 := (le_max_left _ _).trans (le_max_right _ _)
  have hHn0 : H + 1 ≤ n0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKn0 : K ≤ n0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hDn0 : D ≤ n0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hn0R : (D : ℝ) ≤ n0 := by exact_mod_cast hDn0
  have hbase : 400 ≤ eta ^ 2 * (n0 : ℝ) := by
    have hh : 400 / eta ^ 2 < (D : ℝ) := (le_max_left _ _).trans_lt hD
    have hh' := (div_lt_iff₀ hquad).mp hh
    have hm := mul_le_mul_of_nonneg_left hn0R hquad.le
    nlinarith only [hh', hm]
  have hscale : Real.log (3 * B) ≤ (eta ^ 5 * (n0 : ℝ)) * Real.log 2 := by
    have hh : Real.log (3 * B) / (eta ^ 5 * Real.log 2) < (D : ℝ) :=
      (le_max_right _ _).trans_lt hD
    have hden : 0 < eta ^ 5 * Real.log 2 := by positivity
    have hh' := (div_lt_iff₀ hden).mp hh
    have hm := mul_le_mul_of_nonneg_right hn0R hden.le
    nlinarith only [hh', hm]
  have hqle : q ≤ n0 := by omega
  obtain ⟨b0, hb0⟩ := residueProjection_surjective hqle b
  have hb0unit : IsUnit b0 :=
    (residueProjection_isUnit_iff hqle hq b0).mp (by rw [hb0]; exact hb)
  refine ⟨n0, b0, hn02, hb0unit, ?_⟩
  intro R hR
  have hRcoarse : (R : ZMod (3 ^ q)) = b := by
    calc
      (R : ZMod (3 ^ q)) = residueProjection hqle (R : ZMod (3 ^ n0)) :=
        (residueProjection_intCast hqle R).symm
      _ = b := by rw [hR, hb0]
  let n : ℕ → ℕ := fun j => Nat.ceil ((1 + eta) ^ j * (n0 : ℝ))
  have hper : ∀ j : ℕ, ∃ (L : ℕ) (V : Finset Word),
      let tau := (1 + eta) ^ j * (n0 : ℝ) * Real.log (4 / 3 : ℝ)
      1 ≤ n j ∧
      (∀ w ∈ V, w.length = n j - 1 ∧ w.total = L) ∧
      (∀ w ∈ V, Contributes w R) ∧
      Real.exp ((1 - eta ^ 2) * tau) ≤ (3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L ∧
      (3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L ≤ Real.exp ((1 + eta ^ 2) * tau) ∧
      (2 - eta ^ 2) * (n j : ℝ) ≤ (L : ℝ) ∧
      (L : ℝ) ≤ (2 + eta ^ 2) * (n j : ℝ) ∧
      Real.rpow 3 (-(n j : ℝ) - eta ^ 4 * (n j : ℝ)) * (2 : ℝ) ^ L ≤ (V.card : ℝ) ∧
      ∀ w ∈ V, ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
        -eta ^ 5 * (n0 : ℝ) ≤ (inversePrefixTotal w i : ℝ) -
          (i : ℝ) * (Real.log 3 / Real.log 2) := by
    intro j
    let x : ℝ := (1 + eta) ^ j * (n0 : ℝ)
    have hx0 : (n0 : ℝ) ≤ x := by
      have hp : (1 : ℝ) ≤ (1 + eta) ^ j := one_le_pow₀ (by linarith)
      have hn0pos : (0 : ℝ) ≤ n0 := by positivity
      dsimp [x]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hn0pos
    have hxpos : 0 < x := by
      have hn0pos : (0 : ℝ) < n0 := by exact_mod_cast (by omega : 0 < n0)
      exact hn0pos.trans_le hx0
    have hceil : x ≤ (n j : ℝ) := Nat.le_ceil x
    have hceilHi : (n j : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
    have hnn0 : n0 ≤ n j := by exact_mod_cast hx0.trans hceil
    have hn : 1 ≤ n j := by omega
    have hlenH : H ≤ n j - 1 := by omega
    obtain ⟨U, hU, hUcard, hUmass⟩ := hH (n j - 1) hlenH R hRcoarse
    obtain ⟨L, hL, hpigeon⟩ := exists_fixed_total_word_count U R (n j - 1)
      kappa hkappa (fun w hw => (hU w hw).1)
      (fun w hw => (hU w hw).2.1) hUmass
    let V := U.filter (fun w => w.total = L)
    obtain ⟨w0, hw0, hwL⟩ := Finset.mem_image.mp hL
    have hLlo : 2 * ((n j - 1 : ℕ) : ℝ) - (eta ^ 2 / 100) * ((n j - 1 : ℕ) : ℝ) ≤ L := by
      simpa only [delta, hwL] using (hU w0 hw0).2.2.2.1
    have hLhi : (L : ℝ) ≤ 2 * ((n j - 1 : ℕ) : ℝ) +
        (eta ^ 2 / 100) * ((n j - 1 : ℕ) : ℝ) := by
      simpa only [delta, hwL] using (hU w0 hw0).2.2.2.2
    have hbaseX : 400 ≤ eta ^ 2 * x :=
      hbase.trans (mul_le_mul_of_nonneg_left hx0 hquad.le)
    have hbudgets := rounded_balanced_word_budget eta x (n j) L heta hsmall'
      hbaseX hn hceil hceilHi hLlo hLhi
    have hstats : ∀ w ∈ V, w.length = n j - 1 ∧ w.total = L := by
      intro w hw
      obtain ⟨hwU, hwtotal⟩ := Finset.mem_filter.mp hw
      exact ⟨(hU w hwU).1, hwtotal⟩
    have hcontrib : ∀ w ∈ V, Contributes w R := by
      intro w hw
      exact (hU w (Finset.mem_filter.mp hw).1).2.1
    have hcardpos : (0 : ℝ) < (U.image Word.total).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨L, hL⟩
    have hcardupper : ((U.image Word.total).card : ℝ) ≤ 2 * (n j : ℝ) + 1 := by
      have hnat : (U.image Word.total).card ≤ 2 * n j + 1 := hUcard.trans (by omega)
      exact_mod_cast hnat
    have hloss := hK (n j) (hKn0.trans hnn0)
    have hExpBound : Real.exp (-a * (n j : ℝ)) ≤
        (9 / 2 : ℝ) * kappa / ((U.image Word.total).card : ℝ) := by
      apply (le_div_iff₀ hcardpos).mpr
      have hm := mul_le_mul_of_nonneg_right hcardupper (Real.exp_pos (-a * (n j : ℝ))).le
      exact (mul_comm _ _).trans_le (hm.trans hloss)
    have hpigeon' : ((9 / 2 : ℝ) * kappa / ((U.image Word.total).card : ℝ)) *
        ((3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L) ≤ (V.card : ℝ) := by
      rw [word_budget_scale (n j) L hn] at hpigeon
      convert hpigeon using 1 <;> ring
    have hraw : Real.rpow 3 (-(n j : ℝ) - eta ^ 4 * (n j : ℝ)) * (2 : ℝ) ^ L =
        Real.exp (-a * (n j : ℝ)) *
          ((3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L) := by
      rw [Real.rpow_eq_pow, sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        Real.rpow_neg_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      have he : Real.log 3 * -(eta ^ 4 * (n j : ℝ)) = -a * (n j : ℝ) := by dsimp [a]; ring
      rw [he]
      ring
    refine ⟨L, V, hn, hstats, hcontrib, hbudgets.1, hbudgets.2.1,
      hbudgets.2.2.1, hbudgets.2.2.2, ?_, ?_⟩
    · rw [hraw]
      exact (mul_le_mul_of_nonneg_right hExpBound (by positivity)).trans hpigeon'
    · intro w hw i hi hilen
      have hbeta := (hU w (Finset.mem_filter.mp hw).1).2.2.1
      have hh := inverse_prefix_barrier_of_beta w B (eta ^ 5 * (n0 : ℝ))
        hB hbeta hscale i hi hilen
      simpa only [neg_mul] using hh
  choose L V hLV using hper
  exact ⟨n, L, V, hLV⟩

end SyracuseReport

/-! CountingEndToEnd -/

/-! Closed endpoint assembly. Every quantitative input is constructed by
the imported proofs; the paper gate checks the complete endpoint types and
their transitive axioms after these dependencies have compiled. -/

namespace SyracuseReport

theorem paper_admissible_words : PaperStatements.admissible_words :=
  admissible_words_of_actual_balanced_families actual_balanced_cylinder_families

theorem paper_lem_good_roots : PaperStatements.lem_good_roots :=
  good_roots_of_admissible_words paper_admissible_words

theorem paper_thm_counting : PaperStatements.thm_counting :=
  counting_of_good_roots paper_lem_good_roots

theorem paper_cor_uniform : PaperStatements.cor_uniform :=
  paper_cor_uniform_of_counting paper_thm_counting

theorem main_theorem_C : MainTheoremC := paper_cor_uniform atom_floor

end SyracuseReport
