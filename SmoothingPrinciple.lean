import ReportCore
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! A selected-approximation principle on an arbitrary refinement space.
The projection hypothesis is the preservation of a lower bound under
averaging over a refinement fibre. It contains no positivity conclusion.
-/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators

theorem selected_uniform_tail {X : Type*} (g : ℕ → X → ℝ) (E : ℕ → ℝ)
    (hE : Summable E) (hEn : ∀ n, 0 ≤ E n)
    (hstep : ∀ n x, |g (n + 1) x - g n x| ≤ E n)
    (N j : ℕ) (hNj : N ≤ j) (x : X) :
    |g j x - g N x| ≤ ∑' t : ℕ, E (N + t) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNj
  have h := uniform_increment_telescope g E hstep N m x
  have hs : Summable (fun t => E (N + t)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hE
  exact h.trans (hs.sum_le_tsum (Finset.range m) (fun t _ => hEn (N + t)))

/-- Uniformly stabilizing selected subdensities produce one persistent
positive cylinder. The space, refinement relation and density sequence
are arbitrary; no Syracuse law is assumed. -/
theorem selected_positive_cylinder {X : Type*}
    (R : ℕ → X → X → Prop) (eligible : X → Prop)
    (D g : ℕ → X → ℝ) (Q : ℕ → ℕ) (E : ℕ → ℝ) (a : ℝ)
    (ha : 0 < a) (hQ : Tendsto Q atTop atTop)
    (hE : Summable E) (hEn : ∀ n, 0 ≤ E n)
    (hstep : ∀ n x, |g (n + 1) x - g n x| ≤ E n)
    (hselected : ∀ j x, g j x ≤ D (Q j) x)
    (hmark : ∀ j, ∃ y, eligible y ∧ a ≤ g j y)
    (hconstant : ∀ j x y, R (Q j) x y → g j y = g j x)
    (hrefine : ∀ q h, q ≤ h → ∀ y x z, R q y x → R h x z → R q y z)
    (hproject : ∀ j h, h ≤ Q j → ∀ x k,
      (∀ z, R h x z → k ≤ D (Q j) z) → k ≤ D h x) :
    ∃ N y, eligible y ∧ ∀ h, Q N ≤ h → ∀ x,
      R (Q N) y x → a / 2 ≤ D h x := by
  have htail : Tendsto (fun N => ∑' t : ℕ, E (N + t)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add E
  have hsmall : ∀ᶠ N : ℕ in atTop, (∑' t : ℕ, E (N + t)) < a / 2 :=
    (tendsto_order.mp htail).2 _ (by linarith)
  obtain ⟨N, hN⟩ := hsmall.exists
  obtain ⟨y, hy, hmarkN⟩ := hmark N
  refine ⟨N, y, hy, ?_⟩
  intro h hNh x hyx
  have hev : ∀ᶠ j : ℕ in atTop, h ≤ Q j :=
    hQ.eventually (eventually_ge_atTop h)
  obtain ⟨j, hjN, hjh⟩ := (eventually_ge_atTop N).and hev |>.exists
  apply hproject j h hjh x (a / 2)
  intro z hxz
  have hyz := hrefine (Q N) h hNh y x z hyx hxz
  have hsame := hconstant N y z hyz
  have hdiff := selected_uniform_tail g E hE hEn hstep N j hjN z
  have hlower := (abs_le.mp hdiff).1
  rw [hsame] at hlower
  have hsub := hselected j z
  linarith

/-- A finite inverse cover spreads a cylinder bound. Each branch has a
strictly positive transport weight; neither stationarity nor accessibility
is hidden in the conclusion. -/
theorem positive_floor_of_finite_inverse_cover {X I : Type*} [Fintype I] [Nonempty I]
    (D : X → ℝ) (C : Set X) (weight : I → ℝ) (kappa : ℝ)
    (hk : 0 < kappa) (hw : ∀ i, 0 < weight i)
    (hc : ∀ y ∈ C, kappa ≤ D y)
    (hcover : ∀ x, ∃ i y, y ∈ C ∧ weight i * D y ≤ D x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ D x := by
  classical
  obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ weight
    Finset.univ_nonempty
  refine ⟨weight i0 * kappa, mul_pos (hw i0) hk, ?_⟩
  intro x
  obtain ⟨i, y, hy, hxy⟩ := hcover x
  exact (mul_le_mul_of_nonneg_right (hmin i (Finset.mem_univ _)) hk.le).trans
    ((mul_le_mul_of_nonneg_left (hc y hy) (hw i).le).trans hxy)

end SyracuseReport
