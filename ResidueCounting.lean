import Words
import ReportCore
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

namespace SyracuseReport

open scoped BigOperators

/-- The interval count in the report, for arbitrary real endpoints and a
single integer residue class. Endpoints need not themselves be integers. -/
theorem integer_residue_count (s : Finset ℤ) (m r : ℤ) (L U : ℝ)
    (hm : 0 < m) (hLU : L ≤ U)
    (hres : ∀ x ∈ s, x % m = r)
    (hbounds : ∀ x ∈ s, L ≤ (x : ℝ) ∧ (x : ℝ) ≤ U) :
    (s.card : ℝ) ≤ (U - L) / (m : ℝ) + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := Finset.min'_mem s hs
    have hhi : hi ∈ s := Finset.max'_mem s hs
    have hmin : ∀ x ∈ s, lo ≤ x := fun x hx => Finset.min'_le s x hx
    have hmax : ∀ x ∈ s, x ≤ hi := fun x hx => Finset.le_max' s x hx
    have hquot : Set.InjOn (fun x : ℤ => x / m) (s : Set ℤ) := by
      intro x hx y hy hxy
      change x / m = y / m at hxy
      have h1 := Int.mul_ediv_add_emod x m
      have h2 := Int.mul_ediv_add_emod y m
      rw [hres x hx] at h1
      rw [hres y hy, ← hxy] at h2
      linarith
    have hsub : s.image (fun x : ℤ => x / m) ⊆ Finset.Icc (lo / m) (hi / m) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr
        ⟨Int.ediv_le_ediv hm (hmin x hx),
          Int.ediv_le_ediv hm (hmax x hx)⟩
    have horder : lo / m ≤ hi / m :=
      Int.ediv_le_ediv hm (hmin hi hhi)
    have hcard : (s.card : ℤ) ≤ hi / m + 1 - lo / m := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hquot] at hc
      have hc' : (s.card : ℤ) ≤ (Finset.card (Finset.Icc (lo / m) (hi / m)) : ℤ) :=
        by exact_mod_cast hc
      have hsize : (Finset.card (Finset.Icc (lo / m) (hi / m)) : ℤ) = hi / m + 1 - lo / m := Int.card_Icc_of_le (lo / m) (hi / m) (by omega)
      exact hc'.trans_eq hsize
    have hwidth : hi - lo = m * (hi / m - lo / m) := by
      have h1 := Int.mul_ediv_add_emod hi m
      have h2 := Int.mul_ediv_add_emod lo m
      rw [hres hi hhi] at h1
      rw [hres lo hlo] at h2
      nlinarith
    have hcardR : (s.card : ℝ) ≤ (hi / m : ℤ) + 1 - (lo / m : ℤ) :=
      by exact_mod_cast hcard
    have hwidthR : (hi : ℝ) - lo = (m : ℝ) * ((hi / m : ℤ) - (lo / m : ℤ)) :=
      by exact_mod_cast hwidth
    have hLo := (hbounds lo hlo).1
    have hHi := (hbounds hi hhi).2
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have htarget : (s.card : ℝ) - 1 ≤ (U - L) / (m : ℝ) := by
      apply (le_div_iff₀ hmR).mpr
      nlinarith
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ (U - L) / (m : ℝ) := div_nonneg (sub_nonneg.mpr hLU) (by positivity)
    linarith

end SyracuseReport
