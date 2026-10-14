import MixingThresholds
import QuantitativeCounting
import DensitySpikeGeometry
import OffsetLaws
import EntropyObstruction
import SignedReflection

/-! Closed proposition contracts for every theorem added by the full
restructure. These contracts state the mathematics; no result is encoded
as the assumption that its own conclusion holds. -/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

def GeneralSmoothingStatement : Prop :=
  ∀ (X : Type) (R : ℕ → X → X → Prop) (eligible : X → Prop)
    (D g : ℕ → X → ℝ) (Q : ℕ → ℕ) (E : ℕ → ℝ) (a : ℝ),
    0 < a → Tendsto Q atTop atTop → Summable E → (∀ n, 0 ≤ E n) →
    (∀ n x, |g (n + 1) x - g n x| ≤ E n) →
    (∀ j x, g j x ≤ D (Q j) x) →
    (∀ j, ∃ y, eligible y ∧ a ≤ g j y) →
    (∀ j x y, R (Q j) x y → g j y = g j x) →
    (∀ q h, q ≤ h → ∀ y x z, R q y x → R h x z → R q y z) →
    (∀ j h, h ≤ Q j → ∀ x k, (∀ z, R h x z → k ≤ D (Q j) z) → k ≤ D h x) →
    ∃ N y, eligible y ∧ ∀ h, Q N ≤ h → ∀ x, R (Q N) y x → a / 2 ≤ D h x

theorem paper_general_smoothing : GeneralSmoothingStatement := by
  intro X R eligible D g Q E a ha hQ hE hEn hstep hselected hmark hconstant hrefine hproject
  exact selected_positive_cylinder R eligible D g Q E a ha hQ hE hEn
    hstep hselected hmark hconstant hrefine hproject

def FiniteInverseCoverStatement : Prop :=
  ∀ (X I : Type) [Fintype I] [Nonempty I]
    (D : X → ℝ) (C : Set X) (weight : I → ℝ) (kappa : ℝ),
    0 < kappa → (∀ i, 0 < weight i) → (∀ y ∈ C, kappa ≤ D y) →
    (∀ x, ∃ i y, y ∈ C ∧ weight i * D y ≤ D x) →
      ∃ i0 : I, (∀ i, weight i0 ≤ weight i) ∧
        0 < weight i0 * kappa ∧ ∀ x, weight i0 * kappa ≤ D x

theorem paper_finite_inverse_cover : FiniteInverseCoverStatement := by
  intro X I _ _ D C weight kappa hk hw hc hcover
  classical
  obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  refine ⟨i0, fun i => hmin i (Finset.mem_univ _), mul_pos (hw i0) hk, ?_⟩
  intro x
  obtain ⟨i, y, hy, hxy⟩ := hcover x
  exact (mul_le_mul_of_nonneg_right (hmin i (Finset.mem_univ _)) hk.le).trans
    ((mul_le_mul_of_nonneg_left (hc y hy) (hw i).le).trans hxy)

def PolynomialMixingStatement : Prop :=
  ∀ (b E : ℕ → ℝ) (rho theta alpha c C : ℝ),
    1 < rho → 1 / 2 < theta → theta < 1 → theta < alpha →
    0 < c → 0 ≤ C → (∀ n, rho ^ n ≤ b n) → (∀ n, 0 ≤ E n) →
    (∀ n, E n ≤ C * (b n) ^ theta *
      ((b n) ^ (-alpha) + Real.exp (-c * (b n) ^ (2 * theta - 1)))) → Summable E

theorem paper_polynomial_mixing : PolynomialMixingStatement := by
  intro b E rho theta alpha c C hr ht _ hgap hc hC hb hEn he
  exact summable_mean_to_uniform_errors b E rho theta alpha c C hr ht hgap hc hC hb hEn he

def PrefixWindowStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ N, (prefixWindow N : ℝ) ≤ K * (blockLength N : ℝ) ^ (3 / 5 : ℝ)

theorem paper_prefix_window_sharp : PrefixWindowStatement := prefixWindow_power_bound

def WordClockStatement : Prop :=
  ∀ (w : Word) (R : ℤ), Odd R → Contributes w R →
    collatz^[w.total] (inverseInteger w R) = R

theorem paper_word_clock : WordClockStatement := inverse_word_clock

def ExactDimensionStatement : Prop :=
  ∀ mu : Measure (PadicInt 3), IsSyracuseLimit mu →
    ∀ᵐ x ∂mu, Tendsto (localDimensionRatio x) atTop (𝓝 1)

theorem paper_exact_dimension : ExactDimensionStatement := by
  intro mu hmu
  rw [unitDensityMeasure_unique mu hmu]
  exact syracuse_exact_dimension

def DenseSpikesStatement : Prop :=
  Real.log 2 / Real.log 3 < 1 ∧ DenseSpikeGeometryStatement

theorem paper_dense_spikes : DenseSpikesStatement := by
  refine ⟨?_, dense_spike_geometry⟩
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mpr
  simpa only [one_mul] using Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) < 3)

def OffsetLawsStatement : Prop :=
  ∀ u : (PadicInt 3)ˣ,
    (∀ n r, offsetLaw u n r = syracuseLaw n ((unitResidue u n).mulLeft.symm r)) ∧
    (∀ n r, offsetMeasure u (cylinder n r) = offsetLaw u n r) ∧
    (∀ n, offsetLeastAtom u n = leastAtom n) ∧
    Integrable (offsetDensity u) unitHaar ∧
    (∀ᵐ x ∂unitHaar, 0 ≤ offsetDensity u x) ∧
    offsetMeasure u = unitHaar.withDensity (fun x => ENNReal.ofReal (offsetDensity u x)) ∧
    essInf (offsetDensity u) unitHaar = essInf unitDensityFunction unitHaar ∧
    (∀ p : ℝ≥0∞, MemLp (offsetDensity u) p unitHaar ↔ MemLp unitDensityFunction p unitHaar) ∧
    (¬ MemLp (offsetDensity u) 2 unitHaar) ∧
    ∀ q : ℕ, 1 ≤ q → ∀ r : ZMod (3 ^ q), IsUnit r → ∀ M : ℝ,
      0 < unitHaar (cylinder q r ∩ {x | M < offsetDensity u x})

theorem paper_offset_laws : OffsetLawsStatement := by
  intro u
  exact ⟨offsetLaw_apply u, offsetMeasure_cylinder u, offsetLeastAtom_eq u, offsetDensity_integrable u,
    offsetDensity_nonneg u, offsetMeasure_density u, offsetDensity_essInf u,
    offset_memLp_iff u unitDensityFunction, offsetDensity_not_memLp_two u,
    offsetDensity_large_set_positive u⟩

def EntropyObstructionStatement : Prop :=
  ∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)] [∀ n, DecidableEq (X n)]
    (p : (n : ℕ) → X n → ℝ) (S : (n : ℕ) → Finset (X n)) (epsilon : ℕ → ℝ),
    (∀ n, (∑ x ∈ Finset.univ \ S n, p n x) ≤ epsilon n) →
    Tendsto epsilon atTop (𝓝 0) →
    Tendsto (fun n => ((S n).card : ℝ) / Fintype.card (X n)) atTop (𝓝 0) →
      ¬ ∃ delta : ℝ, 0 < delta ∧ ∀ n x, delta / Fintype.card (X n) ≤ p n x

theorem paper_entropy_obstruction : EntropyObstructionStatement := by
  intro X _ _ _ p S epsilon hr he hs
  exact no_uniform_floor_of_small_cover X p S epsilon hr he hs

def GeometricCoverStatement : Prop :=
  ∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    (S : (n : ℕ) → Finset (X n)) (C rho : ℝ),
    0 ≤ rho → rho < 1 →
    (∀ n, ((S n).card : ℝ) / Fintype.card (X n) ≤ C * rho ^ n) →
      Tendsto (fun n => ((S n).card : ℝ) / Fintype.card (X n)) atTop (𝓝 0)

theorem paper_geometric_cover : GeometricCoverStatement := by
  intro X _ _ S C rho hr0 hr1 hbound
  exact small_cover_fraction_of_geometric_bound X S C rho hr0 hr1 hbound

def MinusCountingStatement : Prop :=
  ∀ b : ℤ, 0 < b → ¬(3 : ℤ) ∣ b →
    (∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      x ^ (1 - eps) ≤ (minusPredecessorCount b x : ℝ)) ∧
    Tendsto (fun x : ℝ => Real.log (minusPredecessorCount b x) / Real.log x) atTop (𝓝 1)

theorem paper_minus_counting : MinusCountingStatement := minus_predecessor_exponent

def MinusMapStatement : Prop :=
  ∀ n : ℤ, minusCollatz n = if n % 2 = 0 then n / 2 else (3 * n - 1) / 2

theorem paper_minus_map : MinusMapStatement := by
  intro n
  unfold minusCollatz collatz
  by_cases hn : n % 2 = 0
  · have hneg : (-n) % 2 = 0 := by omega
    rw [if_pos hneg, if_pos hn, Int.neg_ediv_of_dvd (Int.dvd_of_emod_eq_zero hn), neg_neg]
  · have hneg : (-n) % 2 ≠ 0 := by omega
    have heven : (3 * n - 1) % 2 = 0 := by omega
    have hdiv : (2 : ℤ) ∣ 3 * n - 1 := Int.dvd_of_emod_eq_zero heven
    rw [if_neg hneg, if_neg hn, show 3 * (-n) + 1 = -(3 * n - 1) by ring,
      Int.neg_ediv_of_dvd hdiv, neg_neg]

def IntegerOffsetUnitStatement : Prop :=
  ∀ d : ℤ, ¬(3 : ℤ) ∣ d → IsUnit (d : PadicInt 3)

theorem paper_integer_offset_unit : IntegerOffsetUnitStatement := integer_unit_of_not_three

def OffsetConjugacyStatement : Prop :=
  ∀ d z v : PadicInt 3, v * (3 * (d * z) + d) = d * (v * (3 * z + 1))

theorem paper_offset_conjugacy : OffsetConjugacyStatement := by
  intro d z v
  ring

end SyracuseReport
