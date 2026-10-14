import SquareRootFamilies
import SquareRootCutoffs
import QuantitativeCounting

/-! The closed signed square-root-loss predecessor theorem, including the
actual shortcut clock. Positive word mass is constructed, not assumed. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem sqrtLog_budget_bounds (h L : ℕ) (K : ℝ)
    (hlo : 2 * (h : ℝ) - K * sqrtLogProfile h ≤ L)
    (hhi : (L : ℝ) ≤ 2 * (h : ℝ) + K * sqrtLogProfile h) :
    Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * sqrtLogProfile h) ≤
        (2 : ℝ) ^ L / (3 : ℝ) ^ h ∧
      (2 : ℝ) ^ L / (3 : ℝ) ^ h ≤
        Real.exp (Real.log (4 / 3 : ℝ) * h + (K * Real.log 2) * sqrtLogProfile h) := by
  have hlog : Real.log ((2 : ℝ) ^ L / (3 : ℝ) ^ h) =
      (L : ℝ) * Real.log 2 - (h : ℝ) * Real.log 3 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl := mul_le_mul_of_nonneg_right hlo hlog2
  have hh := mul_le_mul_of_nonneg_right hhi hlog2
  constructor
  · apply (Real.le_log_iff_exp_le (by positivity)).mp
    rw [hlog, log_four_thirds_eq]
    nlinarith
  · apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [hlog, log_four_thirds_eq]
    nlinarith

theorem sqrtLog_family_timed_bound
    (V : Finset Word) (R a : ℤ) (hR : Odd R) (h J : ℕ)
    (kappa B K : ℝ) (hk : 0 < kappa) (hK : 0 < K)
    (hseed : collatz^[J] R = a)
    (hprops : ∀ w ∈ V, w.length = h ∧ Contributes w R ∧ w.beta ≤ B ∧
      2 * (h : ℝ) - K * sqrtLogProfile h ≤ (w.total : ℝ) ∧
      (w.total : ℝ) ≤ 2 * (h : ℝ) + K * sqrtLogProfile h)
    (hcard : ((V.image Word.total).card : ℝ) ≤ (2 * K + 1) * ((h : ℝ) + 1))
    (hmass : kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0))
    (hB : 0 < B) :
    (kappa / ((2 * K + 1) * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
        Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * sqrtLogProfile h) ≤
      (timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (Real.log (4 / 3 : ℝ) * h +
          (K * Real.log 2) * sqrtLogProfile h))
        (2 * (h : ℝ) + K * sqrtLogProfile h + J) : ℝ) := by
  classical
  obtain ⟨A, hA, hcount⟩ := exists_fixed_total_word_count V R h kappa hk
    (fun w hw => (hprops w hw).1) (fun w hw => (hprops w hw).2.1) hmass
  obtain ⟨w0, hw0, hwA⟩ := Finset.mem_image.mp hA
  have hAprops := hprops w0 hw0
  rw [hwA] at hAprops
  have hbudget := sqrtLog_budget_bounds h A K hAprops.2.2.2.1 hAprops.2.2.2.2
  have hIpos : (0 : ℝ) < (V.image Word.total).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨A, hA⟩
  have hcoeff : kappa / ((2 * K + 1) * ((h : ℝ) + 1)) ≤
      kappa / ((V.image Word.total).card : ℝ) :=
    div_le_div_of_nonneg_left hk.le hIpos hcard
  have hfactor : 0 ≤ (kappa / ((V.image Word.total).card : ℝ)) * (3 / 2 : ℝ) := by positivity
  have hwords :
      (kappa / ((2 * K + 1) * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
          Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * sqrtLogProfile h) ≤
        ((V.filter (fun w => w.total = A)).card : ℝ) := by
    apply le_trans _ hcount
    exact mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by norm_num)) hbudget.1
      (Real.exp_pos _).le hfactor
  apply hwords.trans
  have hnat : (V.filter (fun w => w.total = A)).card ≤
      timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (Real.log (4 / 3 : ℝ) * h +
          (K * Real.log 2) * sqrtLogProfile h))
        (2 * (h : ℝ) + K * sqrtLogProfile h + J) :=
    word_family_le_timed_count (V.filter (fun w => w.total = A)) R a hR h A J _ _ hseed
    (fun w hw => ⟨(hprops w (Finset.mem_filter.mp hw).1).1, (Finset.mem_filter.mp hw).2⟩)
    (fun w hw => (hprops w (Finset.mem_filter.mp hw).1).2.1)
    (by
      intro w hw
      obtain ⟨hwV, hwA'⟩ := Finset.mem_filter.mp hw
      have hp := hprops w hwV
      have hb := inverseInteger_abs_bound w R hp.2.1 hp.2.2.1
      rw [hp.1, hwA'] at hb
      apply hb.trans
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbudget.2
        (show 0 ≤ |(R : ℝ)| + B by positivity))
    (by push_cast; linarith [hAprops.2.2.2.2])
  exact_mod_cast hnat

def SquareRootCountingStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℤ, ¬(3 : ℤ) ∣ a →
    ∃ D x0 : ℝ, 0 < D ∧ Real.exp 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      c * x * Real.exp (-C * sqrtLogProfile (Real.log x)) ≤
        (timedPredecessorCount a x
          ((2 / Real.log (4 / 3 : ℝ)) * Real.log x +
            D * sqrtLogProfile (Real.log x)) : ℝ)

theorem main_sqrtLog_counting : SquareRootCountingStatement := by
  obtain ⟨q, y, kappa, B, K, H, hq, hy, hkappa, hB, hK, hH, hfamilies⟩ :=
    squareRoot_balanced_families
  let c : ℝ := Real.log (4 / 3 : ℝ)
  let k : ℝ := K * Real.log 2
  let M : ℝ := 2 * K + 1
  let d : ℝ := 8
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hclower : (1/8 : ℝ) ≤ c := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4/3)
    norm_num at h
    dsimp [c]
    linarith
  have hk : 0 < k := mul_pos hK (Real.log_pos (by norm_num))
  have hM : 0 < M := by dsimp [M]; linarith
  have hd : 0 < d := by norm_num [d]
  refine ⟨(kappa * (3 / 2 : ℝ) / M) * Real.exp (-c), 2 * k * d + 3,
    by positivity, by positivity, ?_⟩
  intro a ha
  obtain ⟨R, hR, hRy, hRa, _, _⟩ := signed_seed_in_residue a ha q hq y 0
  obtain ⟨J, hseed⟩ := hRa
  have hQ : 0 < |(R : ℝ)| + B := by positivity
  obtain ⟨x0, hx02, hwitness⟩ := sqrtLog_cutoff_witness c k K kappa M
    (|(R : ℝ)| + B) J H hc hclower hk hK hkappa hM hQ hH
  refine ⟨K * d + J, max (Real.exp 2) x0, by positivity, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨h, hh, hsize, hcount, htime⟩ := hwitness x ((le_max_right _ _).trans hx)
  obtain ⟨V, hprops, hcard, hmass⟩ := hfamilies h hh R hRy
  have hlength := sqrtLog_family_timed_bound V R a hR h J kappa B K
    hkappa hK hseed hprops hcard hmass hB
  have hmono :
      (timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (c * h + k * sqrtLogProfile h))
        (2 * (h : ℝ) + K * sqrtLogProfile h + J) : ℝ) ≤
        timedPredecessorCount a x
          ((2 / c) * Real.log x + (K * d + J) * sqrtLogProfile (Real.log x)) := by
    exact_mod_cast timedPredecessorCount_mono a _ _ _ _ hsize htime
  exact hcount.trans (hlength.trans hmono)

theorem sqrtLog_predecessor_count :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℤ, ¬(3 : ℤ) ∣ a →
      ∃ x0 : ℝ, Real.exp 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
        c * x * Real.exp (-C * sqrtLogProfile (Real.log x)) ≤
          (predecessorCount a x : ℝ) := by
  obtain ⟨c, C, hc, hC, hquant⟩ := main_sqrtLog_counting
  refine ⟨c, C, hc, hC, ?_⟩
  intro a ha
  obtain ⟨D, x0, _, hx02, hx0⟩ := hquant a ha
  refine ⟨x0, hx02, ?_⟩
  intro x hx
  exact (hx0 x hx).trans (by exact_mod_cast timedPredecessorCount_le a x _)

end SyracuseReport
