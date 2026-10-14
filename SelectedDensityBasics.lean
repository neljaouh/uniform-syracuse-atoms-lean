import PaperStatements
import UnitDensityFloor
import BlockGrowth
import WordProbability
set_option backward.isDefEq.respectTransparency false

/-! Mass and positivity of the actual selected-prefix observables. The
selected family is a subfamily of the full word expansion, so its excess
above the Syracuse density is identically zero.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped BigOperators Topology

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem finiteMean_finset_sum {I X : Type*} [Fintype X]
    (s : Finset I) (f : I → X → ℝ) :
    finiteMean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteMean (f i) := by
  unfold finiteMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteMean_wordTransport (w : Word) (q : ℕ) (f : ZMod (3 ^ q) → ℝ) :
    finiteMean (fun r : ZMod (3 ^ (w.length + q)) => wordTransport w q r.val f) =
      w.probability * finiteMean f := by
  have heq : (fun r : ZMod (3 ^ (w.length + q)) => wordTransport w q r.val f) =
      finiteTransport w q f := by
    funext r
    have h := finiteTransport_eq_integer w q f (r.val : ℤ)
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h.symm
  rw [heq, finiteMean_finiteTransport]

theorem finiteMean_wordTransport_at_depth (w : Word) (d q : ℕ)
    (hw : w.length = d) (f : ZMod (3 ^ q) → ℝ) :
    finiteMean (fun r : ZMod (3 ^ (d + q)) => wordTransport w q r.val f) =
      w.probability * finiteMean f := by
  subst d
  exact finiteMean_wordTransport w q f

theorem finiteMean_familyTransport (s : Finset Word) (d q : ℕ)
    (hlen : ∀ w ∈ s, w.length = d) (f : ZMod (3 ^ q) → ℝ) :
    finiteMean (familyTransport s d q f) =
      (∑ w ∈ s, w.probability) * finiteMean f := by
  classical
  unfold familyTransport
  rw [finiteMean_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  exact finiteMean_wordTransport_at_depth w d q (hlen w hw) f

theorem familyTransport_density_le (s : Finset Word) (d q : ℕ)
    (hlen : ∀ w ∈ s, w.length = d) (r : ZMod (3 ^ (d + q))) :
    familyTransport s d q (density q) r ≤ density (d + q) r := by
  classical
  let S : Finset {w : Word // w.length = d} := s.attach.image
    (fun w => (⟨w.1, hlen w.1 w.2⟩ : {w : Word // w.length = d}))
  have hsum : (∑ w ∈ S, wordTransport w.1 q r.val (density q)) =
      ∑ w ∈ s, wordTransport w q r.val (density q) := by
    unfold S
    rw [Finset.sum_image]
    · exact Finset.sum_attach s (fun w : Word =>
        wordTransport w q (r.val : ℤ) (density q))
    · intro w hw v hv h
      apply Subtype.ext
      exact congrArg (fun u : {w : Word // w.length = d} => u.1) h
  have hs := hasSum_fixedLength_density d q (r.val : ℤ)
  have hb := hs.summable.sum_le_tsum S
    (fun w _ => wordTransport_density_nonneg w.1 q (r.val : ℤ))
  rw [hs.tsum_eq, hsum] at hb
  simpa only [familyTransport, Int.cast_natCast, ZMod.natCast_zmod_val] using hb

theorem selectedDepth_positive (N : ℕ) : 1 ≤ selectedDepth N :=
  (terminalDepth_pos N).trans (Nat.le_add_left _ _)

theorem selectedDensity_nonneg (N : ℕ) (r : ZMod (3 ^ selectedDepth N)) :
    0 ≤ selectedDensity N r := by
  classical
  exact Finset.sum_nonneg (fun w _ =>
    wordTransport_density_nonneg w (terminalDepth N) (r.val : ℤ))

theorem selectedDensity_le_density (N : ℕ) (r : ZMod (3 ^ selectedDepth N)) :
    selectedDensity N r ≤ density (selectedDepth N) r :=
  familyTransport_density_le (selectedPrefixes N) (prefixDepth N) (terminalDepth N)
    (fun _ hw => selectedPrefixes_length hw) r

theorem selectedDensity_nonunit (N : ℕ) (r : ZMod (3 ^ selectedDepth N))
    (hr : ¬ IsUnit r) : selectedDensity N r = 0 := by
  apply le_antisymm
  · exact (selectedDensity_le_density N r).trans_eq
      (density_nonunit (selectedDepth_positive N) r hr)
  · exact selectedDensity_nonneg N r

theorem finiteMean_selectedDensity (N : ℕ) :
    finiteMean (selectedDensity N) = (2 / 3 : ℝ) * prefixProbability N := by
  rw [selectedDensity, finiteMean_familyTransport (selectedPrefixes N) (prefixDepth N)
    (terminalDepth N) (fun _ hw => selectedPrefixes_length hw) (density (terminalDepth N)),
    sum_selectedPrefixes_probability, finiteMean_density]
  ring

theorem integral_selectedDensity (N : ℕ) :
    (∫ x, cylinderFunction (selectedDepth N) (selectedDensity N) x ∂unitHaar) =
      prefixProbability N := by
  rw [integral_cylinderFunction_unitHaar (selectedDepth_positive N)
    (selectedDensity N) (selectedDensity_nonunit N), finiteMean_selectedDensity]
  ring

theorem exists_unit_ge_integral_cylinderFunction (n : ℕ) (hn : 1 ≤ n)
    (f : ZMod (3 ^ n) → ℝ) :
    ∃ r : ZMod (3 ^ n), IsUnit r ∧
      (∫ x, cylinderFunction n f x ∂unitHaar) ≤ f r := by
  classical
  obtain ⟨u, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun u : (ZMod (3 ^ n))ˣ => f (u : ZMod (3 ^ n))) Finset.univ_nonempty
  refine ⟨u, u.isUnit, ?_⟩
  have hAE : ∀ᵐ x ∂unitHaar, cylinderFunction n f x ≤ f (u : ZMod (3 ^ n)) := by
    filter_upwards [unitHaar_ae_unitRegion] with x hx
    have hunit1 : IsUnit (PadicInt.toZModPow 1 x) := by
      have heq := congrArg (fun s : Set (PadicInt 3) => x ∈ s)
        unitRegion_eq_unit_reduction
      exact heq.mp hx
    have hunit : IsUnit (PadicInt.toZModPow n x) := by
      apply (residueProjection_isUnit_iff hn (by omega) (PadicInt.toZModPow n x)).mp
      rw [padic_reduction_comp hn x]
      exact hunit1
    obtain ⟨v, hv⟩ := hunit
    exact (show f (PadicInt.toZModPow n x) ≤ f (u : ZMod (3 ^ n)) by
      rw [← hv]
      exact hmax v (Finset.mem_univ v))
  have hInt := integral_mono_ae (integrable_cylinderFunction unitHaar n f)
    (integrable_const (f (u : ZMod (3 ^ n)))) hAE
  simpa only [integral_const, probReal_univ, one_smul] using hInt

theorem selectedDensity_positive_mark (N : ℕ) :
    ∃ r : ZMod (3 ^ selectedDepth N), IsUnit r ∧
      sInf (Set.range prefixProbability) ≤ selectedDensity N r := by
  obtain ⟨r, hr, hmean⟩ := exists_unit_ge_integral_cylinderFunction
    (selectedDepth N) (selectedDepth_positive N) (selectedDensity N)
  rw [integral_selectedDensity] at hmean
  refine ⟨r, hr, le_trans ?_ hmean⟩
  exact csInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact (prefixProbability_pos j).le⟩ ⟨N, rfl⟩

theorem selectedDensity_mean_excess_zero (N : ℕ) :
    finiteMean (fun r : ZMod (3 ^ selectedDepth N) =>
      max (selectedDensity N r - density (selectedDepth N) r) 0) = 0 := by
  have heq : (fun r : ZMod (3 ^ selectedDepth N) =>
      max (selectedDensity N r - density (selectedDepth N) r) 0) = fun _ => 0 := by
    funext r
    exact max_eq_right (sub_nonpos.mpr (selectedDensity_le_density N r))
  rw [heq]
  simp [finiteMean]

end SyracuseReport
