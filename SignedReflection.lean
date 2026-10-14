import CountingCompletion

/-! The positive 3x-1 predecessor interpretation of the signed theorem. -/
namespace SyracuseReport
open Filter
open scoped Topology

def minusCollatz (n : ℤ) : ℤ := -collatz (-n)

theorem minusCollatz_iterate (j : ℕ) (n : ℤ) :
    minusCollatz^[j] n = -(collatz^[j] (-n)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [minusCollatz]

def minusReaches (n b : ℤ) : Prop := ∃ j : ℕ, minusCollatz^[j] n = b

theorem minusReaches_iff (n b : ℤ) : minusReaches n b ↔ Reaches (-n) (-b) := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [minusCollatz_iterate] at hj
    simpa using congrArg Neg.neg hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [minusCollatz_iterate, hj, neg_neg]

theorem collatz_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ collatz n := by
  unfold collatz
  split_ifs <;> apply Int.ediv_nonneg <;> omega

theorem reaches_nonneg {n a : ℤ} (hn : 0 ≤ n) (h : Reaches n a) : 0 ≤ a := by
  obtain ⟨j, rfl⟩ := h
  induction j with
  | zero => exact hn
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact collatz_nonneg ih

noncomputable def minusPredecessorCount (b : ℤ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊x⌋).filter (fun n => minusReaches n b)).card

theorem minusPredecessorCount_eq (b : ℤ) (hb : 0 < b) (x : ℝ) :
    minusPredecessorCount b x = predecessorCount (-b) x := by
  classical
  symm
  unfold minusPredecessorCount predecessorCount
  apply Finset.card_bij (fun n _ => -n)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have hneg : n < 0 := by
      by_contra h
      have ha := reaches_nonneg (by omega : 0 ≤ n) hn.2
      omega
    have hlo : -⌊x⌋ ≤ n := by simpa only [Int.ceil_neg] using hn.1.1
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    apply (minusReaches_iff (-n) b).2
    simpa using hn.2
  · intro n hn m hm hnm
    exact neg_injective hnm
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨-m, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hceil : ⌈-x⌉ = -⌊x⌋ := Int.ceil_neg
    refine ⟨⟨by omega, by omega⟩, (minusReaches_iff m b).1 hm.2⟩

theorem minus_predecessor_exponent (b : ℤ) (hb : 0 < b) (hthree : ¬(3 : ℤ) ∣ b) :
    (∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      x ^ (1 - eps) ≤ (minusPredecessorCount b x : ℝ)) ∧
    Tendsto (fun x : ℝ => Real.log (minusPredecessorCount b x) / Real.log x) atTop (𝓝 1) := by
  have hneg : ¬(3 : ℤ) ∣ -b := by simpa only [dvd_neg] using hthree
  simpa only [minusPredecessorCount_eq b hb] using main_theorem_C (-b) hneg

end SyracuseReport
