import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-! Finite-sum estimates for arithmetic transport operators. -/

namespace SyracuseReport

open scoped BigOperators

noncomputable def finiteMean {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card X

noncomputable def fiberMass {W X : Type*} (s : Finset W) (weight : W → ℝ)
    (source : W → X) (x : X) : ℝ := by
  classical
  exact ∑ w ∈ s, if source w = x then weight w else 0

lemma weighted_sum_by_fibers {W X : Type*} [Fintype X]
    (s : Finset W) (weight : W → ℝ) (source : W → X) (h : X → ℝ) :
    (∑ w ∈ s, weight w * |h (source w)|) =
      ∑ x, fiberMass s weight source x * |h x| := by
  classical
  calc
    (∑ w ∈ s, weight w * |h (source w)|) =
        ∑ w ∈ s, ∑ x : X, if source w = x then weight w * |h x| else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          simp
    _ = ∑ x : X, ∑ w ∈ s, if source w = x then weight w * |h x| else 0 :=
      Finset.sum_comm
    _ = ∑ x, fiberMass s weight source x * |h x| := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [fiberMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      split_ifs <;> simp_all

/-- The normalized finite L1-to-pointwise estimate, conditional on the
coefficient bound for each inverse fiber. The arithmetic specialization is proved in ConcreteKernel.lean. -/
theorem finite_kernel_bound {W X : Type*} [Fintype X]
    (s : Finset W) (weight : W → ℝ) (source : W → X) (h : X → ℝ) (K : ℝ)
    (hweight : ∀ w ∈ s, 0 ≤ weight w)
    (hfiber : ∀ x, fiberMass s weight source x ≤ K / Fintype.card X) :
    |∑ w ∈ s, weight w * h (source w)| ≤
      K * finiteMean (fun x => |h x|) := by
  classical
  calc
    |∑ w ∈ s, weight w * h (source w)| ≤
        ∑ w ∈ s, |weight w * h (source w)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ s, weight w * |h (source w)| := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [abs_mul, abs_of_nonneg (hweight w hw)]
    _ = ∑ x, fiberMass s weight source x * |h x| :=
      weighted_sum_by_fibers s weight source h
    _ ≤ ∑ x : X, (K / Fintype.card X) * |h x| := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hfiber x) (abs_nonneg _)
    _ = K * finiteMean (fun x => |h x|) := by
      rw [← Finset.mul_sum]
      unfold finiteMean
      ring_nf

lemma finiteMean_mono {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : finiteMean f ≤ finiteMean g := by
  unfold finiteMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum (fun x _ => h x)
  · positivity

lemma finiteMean_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    finiteMean (fun x => f x + g x) = finiteMean f + finiteMean g := by
  simp only [finiteMean, Finset.sum_add_distrib, add_div]

/-- The rejected-mass plus mixing-error triangle inequality. -/
theorem block_error_bound {X : Type*} [Fintype X]
    (selected full reference : X → ℝ) (rejected mixing : ℝ)
    (hselected : ∀ x, selected x ≤ full x)
    (hrejected : finiteMean (fun x => full x - selected x) ≤ rejected)
    (hmixing : finiteMean (fun x => |full x - reference x|) ≤ mixing) :
    finiteMean (fun x => |selected x - reference x|) ≤ rejected + mixing := by
  have hpoint : ∀ x, |selected x - reference x| ≤
      (full x - selected x) + |full x - reference x| := by
    intro x
    have htriangle := abs_add_le (selected x - full x) (full x - reference x)
    have habs : |selected x - full x| = full x - selected x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hselected x))]
      ring_nf
    rw [habs] at htriangle
    have heq : selected x - reference x =
        (selected x - full x) + (full x - reference x) := by ring_nf
    rw [heq]
    exact htriangle
  have hmean := finiteMean_mono hpoint
  rw [finiteMean_add] at hmean
  linarith

/-- Finite telescoping for a uniformly bounded increment. -/
theorem uniform_increment_telescope {X : Type*} (g : ℕ → X → ℝ) (E : ℕ → ℝ)
    (hincrement : ∀ n x, |g (n + 1) x - g n x| ≤ E n)
    (m n : ℕ) (x : X) :
    |g (m + n) x - g m x| ≤ ∑ i ∈ Finset.range n, E (m + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htriangle := abs_add_le (g (m + n + 1) x - g (m + n) x)
      (g (m + n) x - g m x)
    have hstep := hincrement (m + n) x
    rw [Finset.sum_range_succ]
    have hidentity : g (m + n + 1) x - g (m + n) x +
        (g (m + n) x - g m x) = g (m + (n + 1)) x - g m x := by
      simp only [Nat.add_assoc]
      ring_nf
    rw [hidentity] at htriangle
    linarith

/-- Conversion from normalized density to an atom lower bound. -/
theorem atom_bound_of_density (n : ℕ) (mass d : ℝ)
    (h : d ≤ (2 / 3 : ℝ) * (3 : ℝ) ^ n * mass) :
    ((3 / 2 : ℝ) * d) / (3 : ℝ) ^ n ≤ mass := by
  have hp : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith

end SyracuseReport
