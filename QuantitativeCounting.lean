import BalancedSubpowerFamilies
import SubpowerCutoffs

/-! Quantitative signed predecessor counts and the actual shortcut clock.
The counted integers are concrete Collatz predecessors, not random words. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def timedPredecessorCount (a : ℤ) (x T : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc ⌈-x⌉ ⌊x⌋).filter
    (fun m => ∃ j : ℕ, (j : ℝ) ≤ T ∧ collatz^[j] m = a)).card

theorem timedPredecessorCount_mono (a : ℤ) (x y S T : ℝ)
    (hxy : x ≤ y) (hST : S ≤ T) :
    timedPredecessorCount a x S ≤ timedPredecessorCount a y T := by
  classical
  apply Finset.card_le_card
  intro m hm
  simp only [timedPredecessorCount, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  obtain ⟨j, hj, hreach⟩ := hm.2
  exact ⟨⟨(Int.ceil_mono (neg_le_neg hxy)).trans hm.1.1,
    hm.1.2.trans (Int.floor_mono hxy)⟩, j, hj.trans hST, hreach⟩

theorem timedPredecessorCount_le (a : ℤ) (x T : ℝ) :
    timedPredecessorCount a x T ≤ predecessorCount a x := by
  classical
  apply Finset.card_le_card
  intro m hm
  simp only [timedPredecessorCount, predecessorCount, Finset.mem_filter] at hm ⊢
  obtain ⟨j, _, hj⟩ := hm.2
  exact ⟨hm.1, j, hj⟩

theorem collatz_iterate_seed_equation {R a : ℤ} {k : ℕ}
    (hk : 1 ≤ k) (hR : Odd R) (he : 3 * R + 1 = (2 : ℤ) ^ k * a) :
    collatz^[k] R = a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Function.iterate_succ_apply, collatz_odd_step (by omega) hR he]
  exact iterate_collatz_two_pow a n

theorem inverse_word_clock (w : Word) (R : ℤ) (hR : Odd R) (hw : Contributes w R) :
    collatz^[w.total] (inverseInteger w R) = R := by
  induction w with
  | nil => simp [Word.total, inverseInteger_nil]
  | snoc w a ih =>
      have hd : Word.snoc w a = w.concat (oneLetterWord a) := rfl
      rw [hd, contributes_concat] at hw
      have hS := (contributing_word_actual_predecessor w R hR hw.1).1
      have he := oneLetter_inverse_equation a (inverseInteger w R) hw.2
      have hM := odd_inverse_of_equation a.pos he
      have hblock := collatz_iterate_seed_equation a.pos hM he
      rw [hd, Word.total_concat, oneLetterWord_total,
        inverseInteger_concat w (oneLetterWord a) R hw.1, Function.iterate_add_apply,
        hblock]
      exact ih hw.1

theorem word_family_le_timed_count (V : Finset Word) (R a : ℤ) (hR : Odd R)
    (h A J : ℕ) (x T : ℝ) (hseed : collatz^[J] R = a)
    (hstats : ∀ w ∈ V, w.length = h ∧ w.total = A)
    (hcon : ∀ w ∈ V, Contributes w R)
    (hsize : ∀ w ∈ V, |(inverseInteger w R : ℝ)| ≤ x)
    (htime : ((A + J : ℕ) : ℝ) ≤ T) :
    V.card ≤ timedPredecessorCount a x T := by
  classical
  have hinj : Set.InjOn (fun w : Word => inverseInteger w R) V := by
    intro w hw v hv he
    exact inverseInteger_injective_fixed_statistics R h A
      ⟨(hstats w hw).1, (hstats w hw).2, hcon w hw⟩
      ⟨(hstats v hv).1, (hstats v hv).2, hcon v hv⟩ he
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro m hm
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hm
  have hbound := abs_le.mp (hsize w hw)
  simp only [timedPredecessorCount, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨Int.ceil_le.mpr hbound.1, Int.le_floor.mpr hbound.2⟩, A + J, htime, ?_⟩
  rw [Nat.add_comm A J, Function.iterate_add_apply, ← (hstats w hw).2,
    inverse_word_clock w R hR (hcon w hw)]
  exact hseed

theorem subpower_budget_bounds (h L : ℕ) (K : ℝ)
    (hlo : 2 * (h : ℝ) - K * (h : ℝ) ^ (3 / 5 : ℝ) ≤ L)
    (hhi : (L : ℝ) ≤ 2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ)) :
    Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)) ≤
        (2 : ℝ) ^ L / (3 : ℝ) ^ h ∧
      (2 : ℝ) ^ L / (3 : ℝ) ^ h ≤
        Real.exp (Real.log (4 / 3 : ℝ) * h + (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)) := by
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

theorem subpower_family_timed_bound
    (V : Finset Word) (R a : ℤ) (hR : Odd R) (h J : ℕ)
    (kappa B K : ℝ) (hk : 0 < kappa) (hK : 0 < K)
    (hseed : collatz^[J] R = a)
    (hprops : ∀ w ∈ V, w.length = h ∧ Contributes w R ∧ w.beta ≤ B ∧
      2 * (h : ℝ) - K * (h : ℝ) ^ (3 / 5 : ℝ) ≤ (w.total : ℝ) ∧
      (w.total : ℝ) ≤ 2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ))
    (hcard : ((V.image Word.total).card : ℝ) ≤ (2 * K + 1) * ((h : ℝ) + 1))
    (hmass : kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0))
    (hB : 0 < B) :
    (kappa / ((2 * K + 1) * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
        Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)) ≤
      (timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (Real.log (4 / 3 : ℝ) * h +
          (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)))
        (2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ) + J) : ℝ) := by
  classical
  obtain ⟨A, hA, hcount⟩ := exists_fixed_total_word_count V R h kappa hk
    (fun w hw => (hprops w hw).1) (fun w hw => (hprops w hw).2.1) hmass
  obtain ⟨w0, hw0, hwA⟩ := Finset.mem_image.mp hA
  have hAprops := hprops w0 hw0
  rw [hwA] at hAprops
  have hbudget := subpower_budget_bounds h A K hAprops.2.2.2.1 hAprops.2.2.2.2
  have hIpos : (0 : ℝ) < (V.image Word.total).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨A, hA⟩
  have hcoeff : kappa / ((2 * K + 1) * ((h : ℝ) + 1)) ≤
      kappa / ((V.image Word.total).card : ℝ) :=
    div_le_div_of_nonneg_left hk.le hIpos hcard
  have hfactor : 0 ≤ (kappa / ((V.image Word.total).card : ℝ)) * (3 / 2 : ℝ) := by positivity
  have hwords :
      (kappa / ((2 * K + 1) * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
          Real.exp (Real.log (4 / 3 : ℝ) * h - (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)) ≤
        ((V.filter (fun w => w.total = A)).card : ℝ) := by
    apply le_trans _ hcount
    exact mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by norm_num)) hbudget.1
      (Real.exp_pos _).le hfactor
  apply hwords.trans
  have hnat : (V.filter (fun w => w.total = A)).card ≤
      timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (Real.log (4 / 3 : ℝ) * h +
          (K * Real.log 2) * (h : ℝ) ^ (3 / 5 : ℝ)))
        (2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ) + J) :=
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

def QuantitativeCountingStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℤ, ¬(3 : ℤ) ∣ a →
    ∃ D x0 : ℝ, 0 < D ∧ 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      c * x * Real.exp (-C * (Real.log x) ^ (3 / 5 : ℝ)) ≤
        (timedPredecessorCount a x
          ((2 / Real.log (4 / 3 : ℝ)) * Real.log x +
            D * (Real.log x) ^ (3 / 5 : ℝ)) : ℝ)

theorem main_quantitative_counting : QuantitativeCountingStatement := by
  obtain ⟨q, y, kappa, B, K, H, hq, hy, hkappa, hB, hK, hH, hfamilies⟩ :=
    subpower_balanced_families
  let c : ℝ := Real.log (4 / 3 : ℝ)
  let k : ℝ := K * Real.log 2
  let M : ℝ := 2 * K + 1
  let d : ℝ := c ^ (-(3 / 5 : ℝ))
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hk : 0 < k := mul_pos hK (Real.log_pos (by norm_num))
  have hM : 0 < M := by dsimp [M]; linarith
  have hd : 0 < d := Real.rpow_pos_of_pos hc _
  refine ⟨(kappa * (3 / 2 : ℝ) / M) * Real.exp (-c), 2 * k * d + 3,
    by positivity, by positivity, ?_⟩
  intro a ha
  obtain ⟨R, hR, hRy, hRa, _, _⟩ := signed_seed_in_residue a ha q hq y 0
  obtain ⟨J, hseed⟩ := hRa
  have hQ : 0 < |(R : ℝ)| + B := by positivity
  obtain ⟨x0, hx02, hwitness⟩ := subpower_cutoff_witness c k K kappa M
    (|(R : ℝ)| + B) J H hc hk hK hkappa hM hQ
  refine ⟨K * d + J, x0, by positivity, hx02, ?_⟩
  intro x hx
  obtain ⟨h, hh, hsize, hcount, htime⟩ := hwitness x hx
  obtain ⟨V, hprops, hcard, hmass⟩ := hfamilies h hh R hRy
  have hlength := subpower_family_timed_bound V R a hR h J kappa B K
    hkappa hK hseed hprops hcard hmass hB
  have hmono :
      (timedPredecessorCount a
        ((|(R : ℝ)| + B) * Real.exp (c * h + k * (h : ℝ) ^ (3 / 5 : ℝ)))
        (2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ) + J) : ℝ) ≤
        timedPredecessorCount a x
          ((2 / c) * Real.log x + (K * d + J) * (Real.log x) ^ (3 / 5 : ℝ)) := by
    exact_mod_cast timedPredecessorCount_mono a _ _ _ _ hsize htime
  exact hcount.trans (hlength.trans hmono)

theorem quantitative_predecessor_count :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℤ, ¬(3 : ℤ) ∣ a →
      ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
        c * x * Real.exp (-C * (Real.log x) ^ (3 / 5 : ℝ)) ≤
          (predecessorCount a x : ℝ) := by
  obtain ⟨c, C, hc, hC, hquant⟩ := main_quantitative_counting
  refine ⟨c, C, hc, hC, ?_⟩
  intro a ha
  obtain ⟨D, x0, _, hx02, hx0⟩ := hquant a ha
  refine ⟨x0, hx02, ?_⟩
  intro x hx
  exact (hx0 x hx).trans (by exact_mod_cast timedPredecessorCount_le a x _)

end SyracuseReport
