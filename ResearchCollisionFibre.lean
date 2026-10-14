import Words
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field

/-! The finite arithmetic part of the quadratic Syracuse cylinder-energy
argument.  These theorems do not assume a collision-energy bound. -/

namespace SyracuseReport
open scoped BigOperators

/-- Among `m` distinct nonnegative integers, the sum of `1 + q` is at
least `m² / 2`.  The induction adds the current maximum. -/
theorem finset_card_sq_le_two_sum_succ (s : Finset ℕ) :
    s.card ^ 2 ≤ 2 * ∑ q ∈ s, (q + 1) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a t hmax ih =>
      have ha : a ∉ t := by
        intro hat
        exact (Nat.lt_irrefl a) (hmax a hat)
      have htcard : t.card ≤ a := by
        have hsub : t ⊆ Finset.range a := by
          intro x hx
          exact Finset.mem_range.mpr (hmax x hx)
        simpa using Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      nlinarith

/-- The same estimate for an injectively labelled finite fibre. -/
theorem fibre_card_sq_le_two_sum_succ {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℕ) (hq : Set.InjOn q s) :
    s.card ^ 2 ≤ 2 * ∑ x ∈ s, (q x + 1) := by
  classical
  have hcard : (s.image q).card = s.card := Finset.card_image_of_injOn hq
  have hsum : (∑ y ∈ s.image q, (y + 1)) = ∑ x ∈ s, (q x + 1) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hq hx hy hxy
  have h := finset_card_sq_le_two_sum_succ (s.image q)
  simpa only [hcard, hsum] using h

/-- Fixed length, fixed total, and a common numerator residue make the
integer quotient by the modulus injective on the word fibre. -/
theorem fixed_total_fibre_quotient_injective (s : Finset Word)
    (d A M r : ℕ) (_hM : 0 < M)
    (hlen : ∀ w ∈ s, w.length = d)
    (htotal : ∀ w ∈ s, w.total = A)
    (hres : ∀ w ∈ s, w.numerator % M = r) :
    Set.InjOn (fun w : Word => w.numerator / M) s := by
  intro w hw v hv hquot
  have hremw := hres w hw
  have hremv := hres v hv
  have hdivw := Nat.mod_add_div w.numerator M
  have hdivv := Nat.mod_add_div v.numerator M
  have hnum : w.numerator = v.numerator := by
    change w.numerator / M = v.numerator / M at hquot
    rw [hremw, hquot] at hdivw
    rw [hremv] at hdivv
    omega
  exact Word.fixed_total_numerator_injective w v
    ((hlen w hw).trans (hlen v hv).symm)
    ((htotal w hw).trans (htotal v hv).symm) hnum

/-- The fixed-total fibre inequality used in the ordinary quadratic
collision-energy proof.  A later module must still sum this over totals
and connect it to the actual finite Syracuse law. -/
theorem fixed_total_residue_fibre_quadratic (s : Finset Word)
    (d A M r : ℕ) (hM : 0 < M)
    (hlen : ∀ w ∈ s, w.length = d)
    (htotal : ∀ w ∈ s, w.total = A)
    (hres : ∀ w ∈ s, w.numerator % M = r) :
    s.card ^ 2 ≤ 2 * ∑ w ∈ s, (w.numerator / M + 1) := by
  exact fibre_card_sq_le_two_sum_succ s (fun w => w.numerator / M)
    (fixed_total_fibre_quotient_injective s d A M r hM hlen htotal hres)

/-- The real form used by the energy calculation: the integer quotient is
at most the corresponding normalized numerator. -/
theorem fixed_total_residue_fibre_quadratic_real (s : Finset Word)
    (d A M r : ℕ) (hM : 0 < M)
    (hlen : ∀ w ∈ s, w.length = d)
    (htotal : ∀ w ∈ s, w.total = A)
    (hres : ∀ w ∈ s, w.numerator % M = r) :
    (s.card : ℝ) ^ 2 ≤
      2 * ∑ w ∈ s, (1 + (w.numerator : ℝ) / (M : ℝ)) := by
  have hnat := fixed_total_residue_fibre_quadratic s d A M r hM hlen htotal hres
  have hnatR : (s.card : ℝ) ^ 2 ≤
      2 * ∑ w ∈ s, (((w.numerator / M + 1 : ℕ) : ℝ)) := by
    have hcast : ((s.card ^ 2 : ℕ) : ℝ) ≤
        (((2 * ∑ w ∈ s, (w.numerator / M + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using hcast
  have hterms : (∑ w ∈ s, (((w.numerator / M + 1 : ℕ) : ℝ))) ≤
      ∑ w ∈ s, (1 + (w.numerator : ℝ) / (M : ℝ)) := by
    apply Finset.sum_le_sum
    intro w _
    have hdiv : (((w.numerator / M : ℕ) : ℝ)) ≤
        (w.numerator : ℝ) / (M : ℝ) := Nat.cast_div_le
    push_cast
    linarith
  exact hnatR.trans (mul_le_mul_of_nonneg_left hterms (by norm_num))

end SyracuseReport
