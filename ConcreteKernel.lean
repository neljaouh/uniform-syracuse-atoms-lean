import ResidueCounting
import Mathlib.Data.ZMod.Basic

namespace SyracuseReport

open scoped BigOperators

/-- The exact integral inverse-fiber equation at the representative `M`. -/
def InverseEquation (w : Word) (M R : ℤ) : Prop :=
  (2 : ℤ) ^ w.total * M - w.numerator = (3 : ℤ) ^ w.length * R

theorem inverse_real_identity (w : Word) (M R : ℤ)
    (h : InverseEquation w M R) : w.coefficient * (R : ℝ) + w.beta = M := by
  have hR : (2 : ℝ) ^ w.total * (M : ℝ) - w.numerator =
      (3 : ℝ) ^ w.length * (R : ℝ) := by exact_mod_cast h
  unfold Word.coefficient Word.beta
  have hp : (2 : ℝ) ^ w.total ≠ 0 := by positivity
  field_simp
  nlinarith

theorem inverse_interval (w : Word) (M R : ℤ) (B : ℝ)
    (h : InverseEquation w M R) (hB : w.beta ≤ B) :
    ((M : ℝ) - B) / w.coefficient ≤ (R : ℝ) ∧
      (R : ℝ) ≤ (M : ℝ) / w.coefficient := by
  have hid := inverse_real_identity w M R h
  have hp := w.coefficient_pos
  constructor
  · apply (div_le_iff₀ hp).mpr
    linarith
  · apply (le_div_iff₀ hp).mpr
    have hb := w.beta_nonneg
    linarith

theorem inverse_injective_at_fixed_total (w v : Word) (M R : ℤ)
    (hd : w.length = v.length) (hA : w.total = v.total)
    (hw : InverseEquation w M R) (hv : InverseEquation v M R) : w = v := by
  apply Word.fixed_total_numerator_injective w v hd hA
  unfold InverseEquation at hw hv
  rw [hd, hA] at hw
  have hn : (w.numerator : ℤ) = v.numerator := by linarith
  exact_mod_cast hn

/-- Arithmetic fiber bound for one total-valuation group. The inverse
integers, interval estimate, and injectivity are checked, not hypotheses. -/
theorem fixed_total_residue_weight (s : Finset Word) (d A : ℕ)
    (M : ℤ) (R : Word → ℤ) (m : ℕ) (r : ℤ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B)
    (hlen : ∀ w ∈ s, w.length = d)
    (htotal : ∀ w ∈ s, w.total = A)
    (hinverse : ∀ w ∈ s, InverseEquation w M (R w))
    (hoffset : ∀ w ∈ s, w.beta ≤ B)
    (hres : ∀ w ∈ s, R w % (m : ℤ) = r) :
    (∑ w ∈ s, w.coefficient) ≤ B / (m : ℝ) + (3 : ℝ) ^ d / (2 : ℝ) ^ A := by
  classical
  let omega : ℝ := (3 : ℝ) ^ d / (2 : ℝ) ^ A
  have hp : 0 < omega := by dsimp [omega]; positivity
  have homega : ∀ w ∈ s, w.coefficient = omega := by
    intro w hw
    simp only [Word.coefficient, hlen w hw, htotal w hw, omega]
  have hRinj : Set.InjOn R (s : Set Word) := by
    intro w hw v hv heq
    exact inverse_injective_at_fixed_total w v M (R w)
      ((hlen w hw).trans (hlen v hv).symm)
      ((htotal w hw).trans (htotal v hv).symm)
      (hinverse w hw) (by rw [heq]; exact hinverse v hv)
  have hcount : ((s.image R).card : ℝ) ≤
      ((M : ℝ) / omega - ((M : ℝ) - B) / omega) / m + 1 := by
    apply integer_residue_count (s.image R) m r
      (((M : ℝ) - B) / omega) ((M : ℝ) / omega) (by exact_mod_cast hm)
    · exact div_le_div_of_nonneg_right (by linarith) hp.le
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact hres w hw
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hb := inverse_interval w M (R w) B (hinverse w hw) (hoffset w hw)
      rwa [homega w hw] at hb
  rw [Finset.card_image_of_injOn hRinj] at hcount
  have hsum : (∑ w ∈ s, w.coefficient) = (s.card : ℝ) * omega := by
    calc
      _ = ∑ _w ∈ s, omega := Finset.sum_congr rfl homega
      _ = _ := by simp
  rw [hsum]
  have hmul := mul_le_mul_of_nonneg_right hcount hp.le
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hpne : omega ≠ 0 := ne_of_gt hp
  have heq : (((M : ℝ) / omega - ((M : ℝ) - B) / omega) / m + 1) * omega =
      B / m + omega := by field_simp; ring
  rw [heq] at hmul
  exact hmul

/-- Sum the actual arithmetic bounds over the distinct total valuations. -/
theorem residue_weight_bound (s : Finset Word) (d : ℕ)
    (M : ℤ) (R : Word → ℤ) (m : ℕ) (r : ℤ) (B Omega : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hOmega : 0 ≤ Omega)
    (hlen : ∀ w ∈ s, w.length = d)
    (hinverse : ∀ w ∈ s, InverseEquation w M (R w))
    (hoffset : ∀ w ∈ s, w.beta ≤ B)
    (hcoefficient : ∀ w ∈ s, w.coefficient ≤ Omega) :
    (∑ w ∈ s with R w % (m : ℤ) = r, w.coefficient) ≤
      ((s.image Word.total).card : ℝ) * (B / m + Omega) := by
  classical
  let t := s.filter (fun w => R w % (m : ℤ) = r)
  let totals := s.image Word.total
  have hpartition :
      (∑ A ∈ totals, ∑ w ∈ t with w.total = A, w.coefficient) =
        ∑ w ∈ t, w.coefficient := by
    apply Finset.sum_fiberwise_of_maps_to
    intro w hw
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hw).1
  change (∑ w ∈ t, w.coefficient) ≤ _
  rw [← hpartition]
  calc
    _ ≤ ∑ _A ∈ totals, (B / m + Omega) := by
      apply Finset.sum_le_sum
      intro A hA
      let u := t.filter (fun w => w.total = A)
      have hus : ∀ w ∈ u, w ∈ s := fun w hw =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
      have hut : ∀ w ∈ u, w.total = A := fun w hw => (Finset.mem_filter.mp hw).2
      by_cases hu : u.Nonempty
      · have hb := fixed_total_residue_weight u d A M R m r B hm hB
          (fun w hw => hlen w (hus w hw)) hut
          (fun w hw => hinverse w (hus w hw))
          (fun w hw => hoffset w (hus w hw))
          (fun w hw => (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2)
        obtain ⟨w, hw⟩ := hu
        have ho : (3 : ℝ) ^ d / (2 : ℝ) ^ A ≤ Omega := by
          have hc := hcoefficient w (hus w hw)
          simpa only [Word.coefficient, hlen w (hus w hw), hut w hw] using hc
        exact hb.trans (by linarith)
      · have he : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
        change (∑ w ∈ u, w.coefficient) ≤ _
        rw [he, Finset.sum_empty]
        exact add_nonneg (div_nonneg hB (by positivity)) hOmega
    _ = _ := by simp [totals]; ring

/-- Weighted residue-counting estimate, with the arithmetic multiplicity
fully proved. The inverse equation is the definition of a contributing
word; it is not a quantitative bound on its multiplicity. -/
theorem weighted_inverse_kernel (s : Finset Word) (d : ℕ)
    (M : ℤ) (R : Word → ℤ) (m : ℕ) [NeZero m] (B Omega : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hOmega : 0 ≤ Omega)
    (hlen : ∀ w ∈ s, w.length = d)
    (hinverse : ∀ w ∈ s, InverseEquation w M (R w))
    (hoffset : ∀ w ∈ s, w.beta ≤ B)
    (hcoefficient : ∀ w ∈ s, w.coefficient ≤ Omega)
    (h : ZMod m → ℝ) :
    |∑ w ∈ s, w.coefficient * h (R w)| ≤
      ((s.image Word.total).card : ℝ) * (B + m * Omega) *
        finiteMean (fun x => |h x|) := by
  classical
  apply finite_kernel_bound s Word.coefficient (fun w => (R w : ZMod m)) h
  · intro w hw
    exact (w.coefficient_pos).le
  · intro x
    have heq : ∀ w, ((R w : ZMod m) = x) ↔ R w % (m : ℤ) = (x.val : ℤ) := by
      intro w
      constructor
      · intro hx
        rw [← ZMod.val_intCast, hx]
      · intro hx
        have hval : (R w : ZMod m).val = x.val := by
          exact_mod_cast (ZMod.val_intCast (R w)).trans hx
        exact ZMod.val_injective m hval
    have hf : fiberMass s Word.coefficient (fun w => (R w : ZMod m)) x =
        ∑ w ∈ s with R w % (m : ℤ) = (x.val : ℤ), w.coefficient := by
      simp only [fiberMass, Finset.sum_filter, heq]
    rw [hf, ZMod.card m]
    have hb := residue_weight_bound s d M R m x.val B Omega hm hB hOmega
      hlen hinverse hoffset hcoefficient
    convert hb using 1; field_simp

def inverseNumerator (w : Word) (M : ℤ) : ℤ :=
  (2 : ℤ) ^ w.total * M - w.numerator

def inverseInteger (w : Word) (M : ℤ) : ℤ :=
  inverseNumerator w M / (3 : ℤ) ^ w.length

def Contributes (w : Word) (M : ℤ) : Prop :=
  (3 : ℤ) ^ w.length ∣ inverseNumerator w M

theorem contributes_inverse_equation (w : Word) (M : ℤ)
    (h : Contributes w M) : InverseEquation w M (inverseInteger w M) := by
  unfold InverseEquation inverseInteger
  exact (Int.mul_ediv_cancel' h).symm

/-- Integer-representative form of the exact word transport in the report. -/
noncomputable def wordTransport (w : Word) (q : ℕ) (M : ℤ)
    (h : ZMod (3 ^ q) → ℝ) : ℝ := by
  classical
  exact if Contributes w M then w.coefficient * h (inverseInteger w M) else 0

/-- Lemma `residue-count` for the actual integer-representative transports.
Only the stated length/offset/coefficient hypotheses remain; no inverse
fiber cardinality or arithmetic injectivity is supplied by the caller. -/
theorem weighted_word_kernel (s : Finset Word) (d q : ℕ) (M : ℤ) (B Omega : ℝ)
    (hB : 0 ≤ B) (hOmega : 0 ≤ Omega)
    (hlen : ∀ w ∈ s, w.length = d)
    (hoffset : ∀ w ∈ s, w.beta ≤ B)
    (hcoefficient : ∀ w ∈ s, w.coefficient ≤ Omega)
    (h : ZMod (3 ^ q) → ℝ) :
    |∑ w ∈ s, wordTransport w q M h| ≤
      ((s.image Word.total).card : ℝ) * (B + (3 ^ q : ℕ) * Omega) *
        finiteMean (fun x => |h x|) := by
  classical
  let t := s.filter (fun w => Contributes w M)
  have hts : ∀ w ∈ t, w ∈ s := fun w hw => (Finset.mem_filter.mp hw).1
  have hb := weighted_inverse_kernel t d M (fun w => inverseInteger w M)
    (3 ^ q) B Omega (by positivity) hB hOmega
    (fun w hw => hlen w (hts w hw))
    (fun w hw => contributes_inverse_equation w M (Finset.mem_filter.mp hw).2)
    (fun w hw => hoffset w (hts w hw))
    (fun w hw => hcoefficient w (hts w hw)) h
  have heq : (∑ w ∈ t, w.coefficient * h (inverseInteger w M)) =
      ∑ w ∈ s, wordTransport w q M h := by
    simp only [t, Finset.sum_filter, wordTransport]
  rw [heq] at hb
  apply hb.trans
  have hc : (t.image Word.total).card ≤ (s.image Word.total).card := by
    apply Finset.card_le_card
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hcR : ((t.image Word.total).card : ℝ) ≤ (s.image Word.total).card :=
    by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hcR
      (add_nonneg hB (mul_nonneg (by positivity) hOmega))
  · unfold finiteMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)

end SyracuseReport
