import ReportCore
import Mathlib.Analysis.SpecificLimits.Basic

/-! A finite-cover obstruction to a uniform floor. No entropy heuristic or
dimension formula is used as an assumption for the conclusion. -/
namespace SyracuseReport
open Filter
open scoped Topology BigOperators

theorem finite_floor_complement_bound {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (p : X → ℝ) (S : Finset X) (delta epsilon : ℝ)
    (hfloor : ∀ x, delta / Fintype.card X ≤ p x)
    (hresidual : (∑ x ∈ Finset.univ \ S, p x) ≤ epsilon) :
    delta * (1 - (S.card : ℝ) / Fintype.card X) ≤ epsilon := by
  classical
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hcard : S.card ≤ Fintype.card X := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ S)
  have hcompl : ((Finset.univ \ S).card : ℝ) = (Fintype.card X : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.cast_sub hcard]
  have hsum := Finset.sum_le_sum (s := Finset.univ \ S) (fun x _ => hfloor x)
  have heq : (∑ _x ∈ Finset.univ \ S, delta / Fintype.card X) =
      delta * (1 - (S.card : ℝ) / Fintype.card X) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcompl]
    field_simp [hN.ne']
    <;> ring
  rw [heq] at hsum
  exact hsum.trans hresidual

theorem no_uniform_floor_of_small_cover
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)] [∀ n, DecidableEq (X n)]
    (p : (n : ℕ) → X n → ℝ) (S : (n : ℕ) → Finset (X n))
    (epsilon : ℕ → ℝ)
    (hresidual : ∀ n, (∑ x ∈ Finset.univ \ S n, p n x) ≤ epsilon n)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hsmall : Tendsto (fun n => ((S n).card : ℝ) / Fintype.card (X n)) atTop (𝓝 0)) :
    ¬ ∃ delta : ℝ, 0 < delta ∧ ∀ n x, delta / Fintype.card (X n) ≤ p n x := by
  rintro ⟨delta, hd, hfloor⟩
  have hbound := fun n => finite_floor_complement_bound (p n) (S n) delta (epsilon n)
    (hfloor n) (hresidual n)
  have hleft : Tendsto (fun n => delta * (1 - ((S n).card : ℝ) / Fintype.card (X n)))
      atTop (𝓝 delta) := by
    have hsub : Tendsto (fun n => (1 : ℝ) - ((S n).card : ℝ) / Fintype.card (X n))
        atTop (𝓝 1) := by
      simpa only [sub_zero] using
        (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hsmall
    simpa only [mul_one] using hsub.const_mul delta
  have hle : delta ≤ 0 := le_of_tendsto_of_tendsto hleft hepsilon
    (Eventually.of_forall hbound)
  linarith

theorem small_cover_fraction_of_geometric_bound
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    (S : (n : ℕ) → Finset (X n)) (C rho : ℝ)
    (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (hbound : ∀ n, ((S n).card : ℝ) / Fintype.card (X n) ≤ C * rho ^ n) :
    Tendsto (fun n => ((S n).card : ℝ) / Fintype.card (X n)) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  apply squeeze_zero (fun n => by positivity) hbound
  simpa only [mul_zero] using hlim

end SyracuseReport
