import MainStatements
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite-cylinder averaging and extraction of a persistent positive
cylinder from the actual Syracuse law and the paper's core estimates.
-/

namespace SyracuseReport
open scoped BigOperators Topology
open Filter

/-- Every residue has exactly the expected number of lifts. -/
theorem residueProjection_fiber_card {Q h : ℕ} (hle : h ≤ Q) (x : ZMod (3 ^ h)) :
    (Finset.univ.filter (fun z : ZMod (3 ^ Q) => residueProjection hle z = x)).card =
      3 ^ (Q - h) := by
  classical
  let P := (residueProjection hle).toAddMonoidHom
  have hs := residueProjection_surjective hle
  have heq (y : ZMod (3 ^ h)) :
      (Finset.univ.filter (fun z : ZMod (3 ^ Q) => P z = y)).card =
      (Finset.univ.filter (fun z : ZMod (3 ^ Q) => P z = x)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range P (hs y) (hs x)
  have ht : Fintype.card (ZMod (3 ^ Q)) =
      ∑ y : ZMod (3 ^ h), (Finset.univ.filter (fun z : ZMod (3 ^ Q) => P z = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun y _ => heq y)] at ht
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card] at ht
  have hp : 3 ^ Q = 3 ^ h * 3 ^ (Q - h) := by rw [← pow_add, Nat.add_sub_of_le hle]
  have ht' : 3 ^ h * 3 ^ (Q - h) = 3 ^ h *
      (Finset.univ.filter (fun z : ZMod (3 ^ Q) => P z = x)).card := hp.symm.trans ht
  exact (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3 ^ h) ht').symm

theorem projection_fiber_constant {Q h : ℕ} (hle : h ≤ Q)
    (x : ZMod (3 ^ h)) (a : ℝ) :
    (∑ z : ZMod (3 ^ Q), if residueProjection hle z = x then a else 0) =
      (3 : ℝ) ^ (Q - h) * a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, residueProjection_fiber_card hle x]
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem projection_fiber_density {Q h : ℕ} (hle : h ≤ Q) (x : ZMod (3 ^ h)) :
    (∑ z : ZMod (3 ^ Q), if residueProjection hle z = x then density Q z else 0) =
      (3 : ℝ) ^ (Q - h) * density h x := by
  have hp : (3 : ℝ) ^ Q = 3 ^ h * 3 ^ (Q - h) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  have he := density_project hle x
  rw [hp] at he
  have hh : (3 : ℝ) ^ h ≠ 0 := by positivity
  have hdiff : (3 : ℝ) ^ (Q - h) ≠ 0 := by positivity
  field_simp at he
  nlinarith

/-- Projecting a one-sided error keeps the conductor h fixed. -/
theorem project_comparison_error {Q h : ℕ} (hle : h ≤ Q)
    (x : ZMod (3 ^ h)) (g : ZMod (3 ^ Q) → ℝ) (kappa : ℝ)
    (hg : ∀ z, residueProjection hle z = x → kappa ≤ g z) :
    kappa ≤ density h x + (3 : ℝ) ^ h *
      finiteMean (fun z => max (g z - density Q z) 0) := by
  classical
  have hb : (∑ z : ZMod (3 ^ Q), if residueProjection hle z = x then kappa else 0) ≤
      (∑ z : ZMod (3 ^ Q), if residueProjection hle z = x then density Q z else 0) +
      ∑ z : ZMod (3 ^ Q), max (g z - density Q z) 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hzx : residueProjection hle z = x
    · simp only [hzx, ite_true]
      have hm := le_max_left (g z - density Q z) 0
      have hk := hg z hzx
      linarith
    · simp only [hzx, ite_false, zero_add]
      exact le_max_right _ _
  rw [projection_fiber_constant, projection_fiber_density] at hb
  have hp : (3 : ℝ) ^ Q = 3 ^ h * 3 ^ (Q - h) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  have hn : (0 : ℝ) < 3 ^ (Q - h) := by positivity
  refine le_of_mul_le_mul_right ?_ hn
  calc
    kappa * 3 ^ (Q - h) ≤ density h x * 3 ^ (Q - h) +
        ∑ z : ZMod (3 ^ Q), max (g z - density Q z) 0 := by nlinarith [hb]
    _ = _ := by
      unfold finiteMean
      rw [ZMod.card]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [hp]
      field_simp


/-- The exact auxiliary estimates of the paper, before their construction. -/
structure CoreWitness where
  depth : ℕ → ℕ
  approximate : (j : ℕ) → ZMod (3 ^ depth j) → ℝ
  mark : ℝ
  excess : ℝ
  variation : ℕ → ℝ
  depth_positive : ∀ j, 1 ≤ j → 1 ≤ depth j
  depth_tendsto : Tendsto depth atTop atTop
  mark_positive : 0 < mark
  excess_nonnegative : 0 ≤ excess
  variation_nonnegative : ∀ N, 1 ≤ N → 0 ≤ variation N
  variation_tendsto : Tendsto variation atTop (𝓝 0)
  positive_mark : ∀ N, 1 ≤ N → ∃ y : ZMod (3 ^ depth N), IsUnit y ∧ mark ≤ approximate N y
  stabilization : ∀ N j, 1 ≤ N → N ≤ j → (hle : depth N ≤ depth j) →
    ∀ z, |approximate j z - approximate N (residueProjection hle z)| ≤ variation N
  mean_excess : ∀ j, 1 ≤ j →
    finiteMean (fun z => max (approximate j z - density (depth j) z) 0) ≤ excess / (j : ℝ)

/-- One fixed unit cylinder has positive density at every finer depth. -/
theorem CoreWitness.positive_cylinder (W : CoreWitness) :
    ∃ (q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
      1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
      ∀ h, (hqh : q ≤ h) → ∀ x : ZMod (3 ^ h),
        residueProjection hqh x = y → kappa ≤ density h x := by
  have hevent : ∀ᶠ N : ℕ in atTop, W.variation N < W.mark / 2 :=
    (tendsto_order.mp W.variation_tendsto).2 _ (by linarith [W.mark_positive])
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hevent
  let N := max N0 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hdelta : W.variation N < W.mark / 2 := hN0 N (le_max_left _ _)
  obtain ⟨y, hy, hmark⟩ := W.positive_mark N hN1
  refine ⟨W.depth N, y, W.mark / 2, W.depth_positive N hN1, hy,
    by linarith [W.mark_positive], ?_⟩
  intro h hqh x hx
  have heventQ : ∀ᶠ j : ℕ in atTop, h ≤ W.depth j :=
    W.depth_tendsto.eventually (Filter.eventually_ge_atTop h)
  have hlower : ∀ᶠ j : ℕ in atTop,
      W.mark / 2 ≤ density h x + (3 : ℝ) ^ h * (W.excess / (j : ℝ)) := by
    filter_upwards [heventQ, Filter.eventually_ge_atTop N] with j hjh hNj
    have hj1 : 1 ≤ j := hN1.trans hNj
    have hpoint := project_comparison_error hjh x (W.approximate j) (W.mark / 2) (by
      intro z hz
      have hsource : residueProjection (hqh.trans hjh) z = y := by
        rw [← residueProjection_comp hjh hqh z, hz, hx]
      have hv := W.stabilization N j hN1 hNj (hqh.trans hjh) z
      rw [hsource] at hv
      have hmin := (abs_le.mp hv).1
      linarith)
    have herror := mul_le_mul_of_nonneg_left (W.mean_excess j hj1)
      (by positivity : (0 : ℝ) ≤ 3 ^ h)
    exact hpoint.trans (by linarith)
  have hratio : Tendsto (fun j : ℕ => W.excess / (j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlimit : Tendsto (fun j : ℕ => density h x + (3 : ℝ) ^ h * (W.excess / (j : ℝ)))
      atTop (𝓝 (density h x)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hratio)
  exact ge_of_tendsto hlimit hlower

end SyracuseReport
