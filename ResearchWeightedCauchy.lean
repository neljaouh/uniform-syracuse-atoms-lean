import ResearchWordMass
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A telescoping-weight version of the finite Cauchy step in the
quadratic collision-energy proof. -/

namespace SyracuseReport
open scoped BigOperators

theorem telescoping_weight_sum (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    (∑ A ∈ Finset.Ico n N,
      (1 : ℝ) / ((A : ℝ) * ((A : ℝ) + 1))) =
      1 / (n : ℝ) - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hle : n ≤ N
      · rw [Finset.sum_Ico_succ_top hle, ih hle]
        have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le hn hle)
        have hN1p : 0 < (N + 1 : ℝ) := by positivity
        have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
        push_cast
        field_simp
        ring
      · have heq : n = N + 1 := by omega
        subst n
        simp

theorem finite_weighted_cauchy (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (u : ℕ → ℝ) :
    (∑ A ∈ Finset.Ico n N, u A) ^ 2 ≤
      (1 / (n : ℝ)) *
        ∑ A ∈ Finset.Ico n N,
          (A : ℝ) * ((A : ℝ) + 1) * (u A) ^ 2 := by
  let s := Finset.Ico n N
  let g : ℕ → ℝ := fun A => 1 / ((A : ℝ) * ((A : ℝ) + 1))
  let h : ℕ → ℝ := fun A => (A : ℝ) * ((A : ℝ) + 1) * (u A) ^ 2
  have hg : ∀ A ∈ s, 0 ≤ g A := by
    intro A _
    dsimp [g]
    positivity
  have hh : ∀ A ∈ s, 0 ≤ h A := by
    intro A _
    dsimp [h]
    positivity
  have hmul : ∀ A ∈ s, (u A) ^ 2 = g A * h A := by
    intro A hAs
    have hAn : n ≤ A := (Finset.mem_Ico.mp hAs).1
    have hAp : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le hn hAn)
    dsimp [g, h]
    field_simp
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hg hh hmul
  have hgsum : (∑ A ∈ s, g A) ≤ 1 / (n : ℝ) := by
    change (∑ A ∈ Finset.Ico n N,
      (1 : ℝ) / ((A : ℝ) * ((A : ℝ) + 1))) ≤ _
    rw [telescoping_weight_sum n N hn hN]
    have hNp : (0 : ℝ) < N := by exact_mod_cast hn.trans hN
    have hnonneg : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith
  have hhsum : 0 ≤ ∑ A ∈ s, h A := Finset.sum_nonneg hh
  calc
    (∑ A ∈ s, u A) ^ 2 ≤ (∑ A ∈ s, g A) * ∑ A ∈ s, h A := hcs
    _ ≤ (1 / (n : ℝ)) * ∑ A ∈ s, h A :=
      mul_le_mul_of_nonneg_right hgsum hhsum

/-- The finite valuation truncation of an actual Syracuse atom is bounded
by the sum of the arithmetic costs of its fixed-total word fibres. -/
theorem finite_atom_fibre_cost_bound (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (R : ℤ) :
    (∑ A ∈ Finset.Ico n N,
      ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A) ^ 2 ≤
      (1 / (n : ℝ)) *
        ∑ A ∈ Finset.Ico n N,
          (A : ℝ) * ((A : ℝ) + 1) *
            ((2 * ∑ w ∈ fixedTotalContributors n A R,
                (1 + (w.numerator : ℝ) / (3 : ℝ) ^ n)) /
              ((2 : ℝ) ^ A) ^ 2) := by
  let u : ℕ → ℝ := fun A =>
    ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A
  have hsum :
      (∑ A ∈ Finset.Ico n N,
        (A : ℝ) * ((A : ℝ) + 1) * (u A) ^ 2) ≤
      ∑ A ∈ Finset.Ico n N,
        (A : ℝ) * ((A : ℝ) + 1) *
          ((2 * ∑ w ∈ fixedTotalContributors n A R,
              (1 + (w.numerator : ℝ) / (3 : ℝ) ^ n)) /
            ((2 : ℝ) ^ A) ^ 2) := by
    apply Finset.sum_le_sum
    intro A _
    have hfibre := actual_fixed_total_fibre_quadratic_real n A R
    have hquot : (u A) ^ 2 ≤
        (2 * ∑ w ∈ fixedTotalContributors n A R,
          (1 + (w.numerator : ℝ) / (3 : ℝ) ^ n)) /
            ((2 : ℝ) ^ A) ^ 2 := by
      dsimp [u]
      rw [div_pow]
      exact div_le_div_of_nonneg_right hfibre (by positivity)
    exact mul_le_mul_of_nonneg_left hquot (by positivity)
  have h := finite_weighted_cauchy n N hn hN u
  calc
    (∑ A ∈ Finset.Ico n N,
      ((fixedTotalContributors n A R).card : ℝ) / (2 : ℝ) ^ A) ^ 2 ≤
        (1 / (n : ℝ)) *
          ∑ A ∈ Finset.Ico n N,
            (A : ℝ) * ((A : ℝ) + 1) * (u A) ^ 2 := by
              simpa only [u] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end SyracuseReport
