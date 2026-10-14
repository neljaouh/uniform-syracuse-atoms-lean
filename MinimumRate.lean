import MinimumLimit

/-! The quantitative O(1/n) exponent error displayed in the manuscript. -/

namespace SyracuseReport

def MinimumRateStatement : Prop :=
  ∀ c : ℝ, 0 < c → FloorAt c →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      |minimumExponent n - 1| ≤ K / ((n + 1 : ℕ) : ℝ)

theorem minimum_exponent_rate : MinimumRateStatement := by
  intro c hc hF
  let L := max |Real.log c| |Real.log (3 / 2 : ℝ)|
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨L / Real.log 3, div_nonneg (le_trans (abs_nonneg _) (le_max_left _ _))
    hlog3.le, ?_⟩
  intro n
  have hlower := normalizedMinimum_lower_of_floor hF n
  have hmpos : 0 < normalizedMinimum n := hc.trans_le hlower
  have hlo := Real.log_le_log hc hlower
  have hhi := Real.log_le_log hmpos (normalizedMinimum_upper n)
  have habs : |Real.log (normalizedMinimum n)| ≤ L := by
    apply abs_le.mpr
    constructor
    · have hL : |Real.log c| ≤ L := le_max_left _ _
      have hneg := neg_abs_le (Real.log c)
      linarith
    · have hL : |Real.log (3 / 2 : ℝ)| ≤ L := le_max_right _ _
      have hpos := le_abs_self (Real.log (3 / 2 : ℝ))
      linarith
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hid : minimumExponent n - 1 =
      -(Real.log (normalizedMinimum n) /
        (((n + 1 : ℕ) : ℝ) * Real.log 3)) := by
    rw [minimumExponent_identity hc hF n]
    ring
  rw [hid, abs_neg, abs_div, abs_of_pos (mul_pos hn hlog3)]
  calc
    |Real.log (normalizedMinimum n)| / (((n + 1 : ℕ) : ℝ) * Real.log 3) ≤
        L / (((n + 1 : ℕ) : ℝ) * Real.log 3) :=
      div_le_div_of_nonneg_right habs (mul_pos hn hlog3).le
    _ = (L / Real.log 3) / ((n + 1 : ℕ) : ℝ) := by
      field_simp

end SyracuseReport
