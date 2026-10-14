import WordFamilyMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Extracting a common valuation total from a finite admissible family. -/

namespace SyracuseReport
open scoped BigOperators

theorem exists_fixed_total_transport_mass (V : Finset Word) (f : Word → ℝ)
    (kappa : ℝ) (hkappa : 0 < kappa) (hmass : kappa ≤ ∑ w ∈ V, f w) :
    ∃ A ∈ V.image Word.total,
      kappa / ((V.image Word.total).card : ℝ) ≤
        ∑ w ∈ V.filter (fun w => w.total = A), f w := by
  classical
  have hV : V.Nonempty := by
    by_contra h
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hmass
    linarith
  have hI : (V.image Word.total).Nonempty := hV.image Word.total
  have hcard : (0 : ℝ) < (V.image Word.total).card := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hpartition :
      (∑ A ∈ V.image Word.total, ∑ w ∈ V.filter (fun w => w.total = A), f w) =
        ∑ w ∈ V, f w :=
    Finset.sum_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image_of_mem Word.total hw) f
  have hconstant : (∑ _A ∈ V.image Word.total,
      kappa / ((V.image Word.total).card : ℝ)) = kappa := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard.ne']
  apply Finset.exists_le_of_sum_le hI
  rw [hconstant, hpartition]
  exact hmass

theorem exists_fixed_total_word_count (V : Finset Word) (R : ℤ) (d : ℕ)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hlen : ∀ w ∈ V, w.length = d)
    (hadmissible : ∀ w ∈ V, Contributes w R)
    (hmass : kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0)) :
    ∃ A ∈ V.image Word.total,
      (kappa / ((V.image Word.total).card : ℝ)) * (3 / 2 : ℝ) *
        ((2 : ℝ) ^ A / (3 : ℝ) ^ d) ≤
          ((V.filter (fun w => w.total = A)).card : ℝ) := by
  classical
  obtain ⟨A, hA, hmassA⟩ := exists_fixed_total_transport_mass V
    (fun w => wordTransport w 0 R (density 0)) kappa hkappa hmass
  refine ⟨A, hA, ?_⟩
  apply card_lower_of_fixed_total_transport (V.filter (fun w => w.total = A)) R d A
    (kappa / ((V.image Word.total).card : ℝ))
  · intro w hw
    have hh := Finset.mem_filter.mp hw
    exact ⟨hlen w hh.1, hh.2⟩
  · intro w hw
    exact hadmissible w (Finset.mem_filter.mp hw).1
  · exact hmassA

end SyracuseReport
