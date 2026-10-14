import DensityRegularity
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Formal consequences of the subcritical-integrability statement in the
separate research report.  This file proves the endpoint and tail steps; it
does not assume that the Syracuse-specific quadratic energy estimate has
already been formalized. -/

namespace SyracuseReport
open MeasureTheory
open scoped ENNReal

theorem lp_critical_exponent_is_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ}
    (hbelow : ∀ q : ℝ, 1 ≤ q → q < 2 → MemLp f (ENNReal.ofReal q) μ)
    (hnot : ¬ MemLp f 2 μ) :
    IsLUB {q : ℝ | 1 ≤ q ∧ MemLp f (ENNReal.ofReal q) μ} 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    by_contra hq2
    have h2q : (2 : ℝ) < q := lt_of_not_ge hq2
    have hmem2 : MemLp f 2 μ := by
      apply hq.2.mono_exponent
      simpa using ENNReal.ofReal_le_ofReal h2q.le
    exact hnot hmem2
  · intro b hb
    by_contra hb2
    have hb2' : b < 2 := lt_of_not_ge hb2
    let q := max (3 / 2 : ℝ) ((b + 2) / 2)
    have hq1 : 1 ≤ q := by
      dsimp [q]
      have : (1 : ℝ) ≤ 3 / 2 := by norm_num
      exact this.trans (le_max_left _ _)
    have hq2 : q < 2 := by
      dsimp [q]
      apply max_lt_iff.mpr
      constructor <;> norm_num <;> linarith
    have hqb : b < q := by
      dsimp [q]
      have hbhalf : b < (b + 2) / 2 := by linarith
      exact lt_of_lt_of_le hbhalf (le_max_right _ _)
    have hqmem : q ∈ {q : ℝ | 1 ≤ q ∧ MemLp f (ENNReal.ofReal q) μ} :=
      ⟨hq1, hbelow q hq1 hq2⟩
    exact (not_lt_of_ge (hb hqmem)) hqb

theorem lp_tail_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ENNReal} (g : Lp ℝ p μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    {t : ENNReal} (ht : t ≠ 0) :
    μ {x | t ≤ ‖g x‖₊} ≤ t⁻¹ ^ p.toReal * ENNReal.ofReal ‖g‖ ^ p.toReal := by
  exact MeasureTheory.Lp.meas_ge_le_mul_pow_enorm g hp0 hptop ht

theorem memLp_tail_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ENNReal} {f : α → ℝ} (hf : MemLp f p μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    {t : ENNReal} (ht : t ≠ 0) :
    μ {x | t ≤ ‖f x‖ₑ} ≤
      t⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  exact MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 hptop
    hf.aestronglyMeasurable ht (by intro _; simp)

theorem subcriticalLp_tail_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hbelow : ∀ q : ℝ, 1 ≤ q → q < 2 → MemLp f (ENNReal.ofReal q) μ)
    (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q < 2)
    {t : ENNReal} (ht : t ≠ 0) :
    μ {x | t ≤ ‖f x‖ₑ} ≤
      t⁻¹ ^ q * eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  have hqpos : 0 < q := by linarith
  have h := memLp_tail_bound (hbelow q hq1 hq2)
    (by positivity) (by simp) ht
  rw [ENNReal.toReal_ofReal hqpos.le] at h
  exact h

end SyracuseReport
