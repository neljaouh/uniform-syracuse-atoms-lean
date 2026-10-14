import Cylinder
import BoundedInverse
import MinimumLimit
import MinimumRate
import Criterion
import BlockFamilies
import Seeds
import TransportAllWords
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

namespace SyracuseReport
open scoped BigOperators Topology
open Filter

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)

/-- Finite output form of the selected word-family transport. -/
noncomputable def familyTransport (s : Finset Word) (d q : ℕ)
    (f : ZMod (3 ^ q) → ℝ) (r : ZMod (3 ^ (d + q))) : ℝ :=
  ∑ w ∈ s, wordTransport w q r.val f

/-- Observable depth and selected subdensity of the manuscript's construction. -/
def selectedDepth (N : ℕ) : ℕ := prefixDepth N + terminalDepth N

noncomputable def selectedDensity (N : ℕ) : ZMod (3 ^ selectedDepth N) → ℝ :=
  familyTransport (selectedPrefixes N) (prefixDepth N) (terminalDepth N)
    (density (terminalDepth N))

noncomputable def selectedKernelConstant (N : ℕ) : ℝ :=
  ((4 : ℝ) * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1) *
    ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength)

noncomputable def selectedIncrementBound (C6 : ℝ) (N : ℕ) : ℝ :=
  (2 / 3 : ℝ) * selectedKernelConstant N *
    (C6 / (terminalDepth N : ℝ) ^ 6 + (1 - blockProbability N))

/-- The exponent-one hypothesis used in the manuscript's counting reduction. -/
def AtomExponentOne : Prop := Tendsto minimumExponent atTop (𝓝 1)

/-- Signed odd predecessors of an odd root, restricted to the root's sign. -/
noncomputable def oddRootPredecessorCount (R : ℤ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc ⌈-x⌉ ⌊x⌋).filter fun m =>
    Odd m ∧ Reaches m R ∧ 0 < m * R).card

/-- Sum of the first `i` inverse-order valuations (outermost first). -/
def inversePrefixTotal (w : Word) (i : ℕ) : ℕ :=
  (((w.letters.reverse.take i).map fun a => (a : ℕ))).sum

/-- Cylinder form of stationarity for the affine Syracuse Markov operator. -/
def IsSyracuseStationary (ρ : MeasureTheory.Measure (PadicInt 3)) : Prop :=
  MeasureTheory.IsProbabilityMeasure ρ ∧
    ∀ (n : ℕ) (r : ZMod (3 ^ (n + 1))),
      ρ (cylinder (n + 1) r) =
        ∑' a : ℕ+, letterLaw a *
          ∑ z : ZMod (3 ^ n),
            if affineStep n a z = r then ρ (cylinder n z) else 0

/-- Normalized additive Haar probability, characterized on ternary cylinders. -/
def IsAdditiveHaar (lam : MeasureTheory.Measure (PadicInt 3)) : Prop :=
  MeasureTheory.IsProbabilityMeasure lam ∧
    ∀ (n : ℕ) (r : ZMod (3 ^ n)),
      lam (cylinder n r) = ENNReal.ofReal (1 / (3 : ℝ) ^ n)

namespace PaperStatements

/-- Projection identity, in probability and normalized-density form. -/
def lem_projection : Prop :=
  ∀ (k h : ℕ) (hle : h ≤ k), 1 ≤ h → ∀ r : ZMod (3 ^ h),
    (syracuseLaw h r = ∑ z : ZMod (3 ^ k),
      if residueProjection hle z = r then syracuseLaw k z else 0) ∧
    (density h r = ((3 : ℝ) ^ h / (3 : ℝ) ^ k) *
      ∑ z : ZMod (3 ^ k), if residueProjection hle z = r then density k z else 0) ∧
    (Finset.univ.filter (fun z : ZMod (3 ^ k) => residueProjection hle z = r)).card = 3 ^ (k - h)

/-- The comparison-error lemma at a fixed test conductor. -/
def lem_error_projection : Prop :=
  ∀ (Q h : ℕ) (hle : h ≤ Q), 1 ≤ h → ∀ (x : ZMod (3 ^ h))
    (g : ZMod (3 ^ Q) → ℝ) (kappa : ℝ),
    (∀ z, residueProjection hle z = x → kappa ≤ g z) →
    kappa ≤ density h x + (3 : ℝ) ^ h *
      finiteMean (fun z => max (g z - density Q z) 0)

/-- The cylinder extraction is conditional on the paper's core estimates. -/
def prop_cylinder : Prop :=
  Nonempty CoreWitness → ∃ (q : ℕ) (y : ZMod (3 ^ q)) (kappa : ℝ),
    1 ≤ q ∧ IsUnit y ∧ 0 < kappa ∧
    ∀ h, (hqh : q ≤ h) → ∀ x : ZMod (3 ^ h),
      residueProjection hqh x = y → kappa ≤ density h x

/-- The bounded inverse step used to spread one positive cylinder. -/
def lem_inverse : Prop :=
  ∀ (h q : ℕ) (hqh : q ≤ h), ∀ (y : ZMod (3 ^ q))
    (r : ZMod (3 ^ (h + 1))), IsUnit r →
    ∃ (v : ℕ+) (z : ZMod (3 ^ h)),
      (v : ℕ) ≤ 2 * 3 ^ q ∧ residueProjection hqh z = y ∧
        affineStep h v z = r

/-- The cylinder criterion gives a uniform atom floor. -/
def prop_criterion_floor : Prop := Nonempty CoreWitness → AtomFloorStatement

/-- Tao's fine-scale mixing input in the normalization of the manuscript. -/
def thm_mixing : Prop :=
  ∀ A : ℕ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
      finiteMean (fun r : ZMod (3 ^ n) =>
        |density n r - density m (residueProjection hmn r)|) ≤
        (2 / 3 : ℝ) * C / (m : ℝ) ^ A

/-- Positivity, normalized mass, lifting, composition and the complete
fixed-length word decomposition of the Syracuse density. -/
def lem_transport : Prop :=
  (∀ (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ),
      (∀ z, 0 ≤ h z) → ∀ r, 0 ≤ finiteTransport w q h r) ∧
  (∀ (w : Word) (q : ℕ) (h : ZMod (3 ^ q) → ℝ),
      finiteMean (finiteTransport w q h) = w.probability * finiteMean h ∧
      finiteMean (fun r => |finiteTransport w q h r|) =
        w.probability * finiteMean (fun z => |h z|)) ∧
  (∀ (w : Word) (q t : ℕ) (hqt : t ≤ q) (h : ZMod (3 ^ t) → ℝ) r,
      finiteTransport w q (fun z => h (residueProjection hqt z)) r =
        finiteTransport w t h
          (residueProjection (Nat.add_le_add_left hqt w.length) r)) ∧
  (∀ (w v : Word) (q : ℕ) (M : ℤ) (h : ZMod (3 ^ q) → ℝ),
      wordTransport (w.concat v) q M h =
        wordTransport w (v.length + q) M (finiteTransport v q h)) ∧
  (∀ (d t : ℕ) (M : ℤ),
      density (d + t) (M : ZMod (3 ^ (d + t))) =
        ∑' w : Word, if w.length = d then wordTransport w t M (density t) else 0)

/-- The fixed-block acceptance probabilities, their exponential rejection
bound, and positivity of the infimum of the finite products. -/
def lem_block_probability : Prop :=
  (∀ j, 0 < blockProbability j ∧ blockProbability j ≤ 1 ∧
    1 - blockProbability j ≤
      2 * Real.exp (-((blockLength j : ℝ) ^ (1 / 5 : ℝ)) / 12)) ∧
  0 < sInf (Set.range prefixProbability)

/-- Fixed length and total valuation determine a word from its offset. -/
def lem_offset_injective : Prop :=
  ∀ (d A : ℕ) (w v : Word), w.length = d → v.length = d →
    w.total = A → v.total = A → w.beta = v.beta → w = v

/-- The full finite L1-to-L-infinity residue-counting statement. -/
def lem_residue_count : Prop :=
  ∀ (s : Finset Word) (d q : ℕ) (B Omega : ℝ), 1 ≤ q →
    (∀ w ∈ s, w.length = d) → (∀ w ∈ s, w.beta ≤ B) →
    (∀ w ∈ s, w.coefficient ≤ Omega) → ∀ f : ZMod (3 ^ q) → ℝ,
    ‖familyTransport s d q f‖ ≤
      ((s.image Word.total).card : ℝ) * (B + (3 ^ q : ℕ) * Omega) *
        finiteMean (fun x => |f x|)

/-- General kernel estimate conditional on supplied affine and cardinality bounds.
This helper alone does not prove the manuscript's selected-prefix estimate. -/
def kernel_bound_from_affine_bounds : Prop :=
  ∀ (s : Finset Word) (d q L : ℕ) (B Omega Lambda : ℝ), 0 ≤ Lambda → 1 ≤ q →
    (∀ w ∈ s, w.length = d) → (∀ w ∈ s, w.beta ≤ B) →
    (∀ w ∈ s, w.coefficient ≤ Omega) →
    (s.image Word.total).card ≤ L →
    (L : ℝ) * (B + (3 ^ q : ℕ) * Omega) ≤ Lambda →
    ∀ f : ZMod (3 ^ q) → ℝ,
      ‖familyTransport s d q f‖ ≤ Lambda * finiteMean (fun x => |f x|)

/-- The manuscript's actual selected-prefix bound, with its explicit constant.
No affine estimate or valuation-window bound is supplied as a hypothesis. -/
def lem_kernel_bound : Prop :=
  ∀ (N q : ℕ), 1 ≤ q → q ≤ 2 * blockLength N →
    ∀ f : ZMod (3 ^ q) → ℝ,
      ‖familyTransport (selectedPrefixes N) (prefixDepth N) q f‖ ≤
        ((4 : ℝ) * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1) *
          ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) *
            finiteMean (fun x => |f x|)

/-- Monotonicity, positive-limit equivalence, relative asymptotics and exponent. -/
def prop_minimum : Prop := MinimumAsymptoticsStatement ∧ MinimumRateStatement

/-- The actual selected observables satisfy the core estimates with the
specified mark, zero excess, and the displayed summable-increment tails. -/
def thm_construction : Prop :=
  ∃ (C6 : ℝ) (W : CoreWitness), 0 ≤ C6 ∧
    W.mark = sInf (Set.range prefixProbability) ∧ W.excess = 0 ∧
    Summable (selectedIncrementBound C6) ∧
    ∀ N : ℕ, 1 ≤ N →
      W.depth N = selectedDepth N ∧
      HEq (W.approximate N) (selectedDensity N) ∧
      W.variation N = ∑' j : ℕ, selectedIncrementBound C6 (N + j)

/-- Every ternary residue contains arbitrarily large same-sign odd seeds
which reach an arbitrary target prime to three. -/
def lem_seeds : Prop :=
  ∀ (a : ℤ), ¬(3 : ℤ) ∣ a → ∀ (q : ℕ), 1 ≤ q →
    ∀ (y : ZMod (3 ^ q)) (B : ℕ),
      ∃ R : ℤ, Odd R ∧ (R : ZMod (3 ^ q)) = y ∧ Reaches R a ∧
        0 < a * R ∧ (B : ℤ) < |R|

/-- Tao's word estimates converted to signed odd-root counts. -/
def lem_good_roots : Prop :=
  AtomExponentOne → ∀ γ : ℝ, γ < 1 →
    ∃ (q : ℕ) (y : ZMod (3 ^ q)), 1 ≤ q ∧ IsUnit y ∧
      ∀ R : ℤ, Odd R → (R : ZMod (3 ^ q)) = y →
        ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
          x ^ γ ≤ (oddRootPredecessorCount R x : ℝ)

/-- The minimum-atom exponent implies the full signed counting theorem. -/
def thm_counting : Prop := AtomExponentOne → MainTheoremC

/-- A uniform atom floor is sufficient for the full signed counting theorem. -/
def cor_uniform : Prop := AtomFloorStatement → MainTheoremC

/-- Quantitative admissible-word input under the minimum-atom hypothesis.
The unit class is fixed; admissible families may depend on the chosen root. -/
def admissible_words : Prop :=
  AtomExponentOne → ∃ η0 : ℝ, 0 < η0 ∧ η0 < 1 ∧
    ∀ η : ℝ, 0 < η → η < η0 →
    ∃ (n0 : ℕ) (b : ZMod (3 ^ n0)), 2 ≤ n0 ∧ IsUnit b ∧
    ∀ R : ℤ, (R : ZMod (3 ^ n0)) = b →
    ∃ (n L : ℕ → ℕ) (V : ℕ → Finset Word),
      ∀ j : ℕ,
        let τ := (1 + η) ^ j * (n0 : ℝ) * Real.log (4 / 3 : ℝ)
        1 ≤ n j ∧
        (∀ w ∈ V j, w.length = n j - 1 ∧ w.total = L j) ∧
        (∀ w ∈ V j, Contributes w R) ∧
        Real.exp ((1 - η ^ 2) * τ) ≤
          (3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L j ∧
        (3 : ℝ) ^ (-(n j : ℤ)) * (2 : ℝ) ^ L j ≤
          Real.exp ((1 + η ^ 2) * τ) ∧
        (2 - η ^ 2) * (n j : ℝ) ≤ (L j : ℝ) ∧
        (L j : ℝ) ≤ (2 + η ^ 2) * (n j : ℝ) ∧
        Real.rpow 3 (-((n j : ℝ)) - η ^ 4 * (n j : ℝ)) *
            (2 : ℝ) ^ L j ≤ ((V j).card : ℝ) ∧
        ∀ w ∈ V j, ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
          -η ^ 5 * (n0 : ℝ) ≤
            (inversePrefixTotal w i : ℝ) -
              (i : ℝ) * (Real.log 3 / Real.log 2)

/-- Existence and uniqueness of the stationary Syracuse probability law. -/
def lem_stationary : Prop :=
  ∃ μ : MeasureTheory.Measure (PadicInt 3),
    IsSyracuseLimit μ ∧ IsSyracuseStationary μ ∧
      ∀ ρ : MeasureTheory.Measure (PadicInt 3), IsSyracuseStationary ρ → ρ = μ

/-- The Syracuse limit law has pure type relative to normalized additive Haar. -/
def lem_pure : Prop :=
  ∀ (μ lam : MeasureTheory.Measure (PadicInt 3)),
    IsSyracuseLimit μ → IsAdditiveHaar lam →
        MeasureTheory.Measure.AbsolutelyContinuous μ lam ∨
          MeasureTheory.Measure.MutuallySingular μ lam

/-- A uniform finite-level atom floor is equivalent to an almost-everywhere
lower bound for the density with respect to unit Haar probability. -/
def prop_haar : Prop :=
  ∀ (μ H : MeasureTheory.Measure (PadicInt 3)),
    IsSyracuseLimit μ → IsUnitHaar H → ∀ c : ℝ, 0 < c →
      (FloorAt c ↔ ∃ f : PadicInt 3 → ℝ,
        MeasureTheory.Integrable f H ∧ (∀ᵐ x ∂H, 0 ≤ f x) ∧
        μ = H.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ᵐ x ∂H, (2 / 3 : ℝ) * c ≤ f x)

/-- Exact logical strength of the auxiliary cylinder criterion. -/
def prop_converse : Prop := Nonempty CoreWitness ↔ AtomFloorStatement

end PaperStatements

theorem paper_lem_projection : PaperStatements.lem_projection := by
  intro k h hle _ r
  exact ⟨syracuseLaw_project_atoms hle r, density_project hle r, residueProjection_fiber_card hle r⟩

theorem paper_lem_error_projection : PaperStatements.lem_error_projection := by
  intro Q h hle _ x g kappa hg
  exact project_comparison_error hle x g kappa hg

theorem paper_prop_cylinder : PaperStatements.prop_cylinder := by
  rintro ⟨W⟩
  exact W.positive_cylinder

theorem paper_lem_inverse : PaperStatements.lem_inverse := by
  intro h q hqh y r hr
  exact bounded_inverse_into_cylinder q h hqh y r hr

theorem paper_prop_criterion_floor : PaperStatements.prop_criterion_floor := by
  rintro ⟨W⟩
  exact atomFloor_of_coreWitness W

/-- Four clauses of the transport lemma are already unconditional. The only
remaining clause is the all-word density decomposition. -/
theorem paper_lem_transport_of_density_decomposition
    (hall : ∀ (d t : ℕ) (M : ℤ),
      density (d + t) (M : ZMod (3 ^ (d + t))) =
        ∑' w : Word, if w.length = d then wordTransport w t M (density t) else 0) :
    PaperStatements.lem_transport := by
  refine ⟨?_, ?_, ?_, ?_, hall⟩
  · intro w q h hh r
    exact finiteTransport_nonneg w q h hh r
  · intro w q h
    exact ⟨finiteMean_finiteTransport w q h,
      finiteMean_abs_finiteTransport w q h⟩
  · intro w q t hqt h r
    exact finiteTransport_lift w hqt h r
  · intro w v q M h
    exact wordTransport_concat w v q M h

theorem paper_lem_transport : PaperStatements.lem_transport :=
  paper_lem_transport_of_density_decomposition density_word_decomposition

theorem paper_lem_offset_injective : PaperStatements.lem_offset_injective := by
  intro d A w v hwd hvd hwA hvA hb
  exact Word.fixed_total_beta_injective w v (hwd.trans hvd.symm) (hwA.trans hvA.symm) hb

theorem paper_lem_residue_count : PaperStatements.lem_residue_count := by
  intro s d q B Omega _ hlen hoffset hcoefficient f
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨w, hw⟩ := hs
    have hB : 0 ≤ B := w.beta_nonneg.trans (hoffset w hw)
    have hOmega : 0 ≤ Omega := w.coefficient_pos.le.trans (hcoefficient w hw)
    have hm : 0 ≤ finiteMean (fun x => |f x|) := by
      unfold finiteMean
      exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
    have hK : 0 ≤ ((s.image Word.total).card : ℝ) *
        (B + (3 ^ q : ℕ) * Omega) * finiteMean (fun x => |f x|) := by positivity
    apply (pi_norm_le_iff_of_nonneg hK).mpr
    intro r
    simpa only [familyTransport, Real.norm_eq_abs] using
      weighted_word_kernel s d q r.val B Omega hB hOmega hlen hoffset hcoefficient f
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hz : familyTransport ∅ d q f = 0 := by
      funext r
      simp only [familyTransport, Finset.sum_empty, Pi.zero_apply]
    rw [hz]
    simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero, zero_mul, norm_zero, le_refl]

theorem kernel_bound_from_affine_bounds :
    PaperStatements.kernel_bound_from_affine_bounds := by
  intro s d q L B Omega Lambda hLambda0 hq hlen hoffset hcoefficient hcard hLambda f
  have hbase := paper_lem_residue_count s d q B Omega hq hlen hoffset hcoefficient f
  have hm : 0 ≤ finiteMean (fun x => |f x|) := by
    unfold finiteMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
  have hcardR : ((s.image Word.total).card : ℝ) ≤ L := by exact_mod_cast hcard
  by_cases hs : s.Nonempty
  · obtain ⟨w, hw⟩ := hs
    have hB : 0 ≤ B := w.beta_nonneg.trans (hoffset w hw)
    have hOmega : 0 ≤ Omega := w.coefficient_pos.le.trans (hcoefficient w hw)
    calc
      ‖familyTransport s d q f‖ ≤
          ((s.image Word.total).card : ℝ) * (B + (3 ^ q : ℕ) * Omega) *
            finiteMean (fun x => |f x|) := hbase
      _ ≤ (L : ℝ) * (B + (3 ^ q : ℕ) * Omega) *
            finiteMean (fun x => |f x|) := by gcongr
      _ ≤ Lambda * finiteMean (fun x => |f x|) := by gcongr
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hz : familyTransport ∅ d q f = 0 := by
      funext r
      simp [familyTransport]
    rw [hz, norm_zero]
    exact mul_nonneg hLambda0 hm

theorem paper_prop_minimum : PaperStatements.prop_minimum :=
  ⟨minimum_asymptotics, minimum_exponent_rate⟩

theorem atomExponentOne_of_floor : AtomFloorStatement → AtomExponentOne := by
  rintro ⟨c, hc, hF⟩
  obtain ⟨_, _, _, _, _, hexponent⟩ :=
    minimum_asymptotics.2.2 c hc hF
  exact hexponent

/-- Once the counting reduction is available, its uniform-floor corollary
is a formal consequence of the least-atom asymptotics already proved. -/
theorem paper_cor_uniform_of_counting (hcount : PaperStatements.thm_counting) :
    PaperStatements.cor_uniform := by
  intro hfloor
  exact hcount (atomExponentOne_of_floor hfloor)

theorem paper_lem_seeds : PaperStatements.lem_seeds := by
  intro a ha q hq y B
  exact signed_seed_in_residue a ha q hq y B

theorem paper_prop_converse : PaperStatements.prop_converse := by
  constructor
  · rintro ⟨W⟩
    exact atomFloor_of_coreWitness W
  · rintro ⟨c, hc, hF⟩
    exact coreWitness_of_floor hc hF

end SyracuseReport
