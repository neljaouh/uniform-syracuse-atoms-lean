import HaarCylinderBasis
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Construction of the limiting probability by compactness. Finite laws are
lifted to their least nonnegative integer representatives. Consistency gives
nonempty nested closed conditions on the compact space of probabilities.
-/
namespace SyracuseReport
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def liftedLaw (n : ℕ) : PMF (PadicInt 3) :=
  (syracuseLaw n).map (fun r => (r.val : PadicInt 3))

theorem liftedLaw_cylinder {n k : ℕ} (hkn : k ≤ n) (r : ZMod (3 ^ k)) :
    (liftedLaw n).toMeasure (cylinder k r) = syracuseLaw k r := by
  classical
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_cylinder k r)]
  rw [liftedLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, tsum_fintype]
  rw [syracuseLaw_project_atoms hkn r]
  apply Finset.sum_congr rfl
  intro z _
  have hz : PadicInt.toZModPow k (z.val : PadicInt 3) = residueProjection hkn z := by
    rw [← padic_reduction_comp hkn]
    congr 1
    simp only [map_natCast, ZMod.natCast_zmod_val]
  simp only [Set.indicator_apply, Set.mem_preimage, cylinder, Set.mem_setOf_eq]
  rw [hz]

theorem continuous_cylinder_mass (n : ℕ) (r : ZMod (3 ^ n)) :
    Continuous (fun ν : ProbabilityMeasure (PadicInt 3) => ν (cylinder n r)) := by
  apply continuous_iff_continuousAt.mpr
  intro ν
  exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    continuousAt_id (isClopen_cylinder n r)

noncomputable def finiteLawConditions (N : ℕ) : Set (ProbabilityMeasure (PadicInt 3)) :=
  {ν | ∀ k, k ≤ N → ∀ r : ZMod (3 ^ k),
    ν (cylinder k r) = (syracuseLaw k r).toNNReal}

theorem finiteLawConditions_isClosed (N : ℕ) : IsClosed (finiteLawConditions N) := by
  change IsClosed {ν : ProbabilityMeasure (PadicInt 3) |
    ∀ k, k ≤ N → ∀ r : ZMod (3 ^ k),
      ν (cylinder k r) = (syracuseLaw k r).toNNReal}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro _hk
  apply isClosed_iInter
  intro r
  exact isClosed_eq (continuous_cylinder_mass k r) continuous_const

theorem finiteLawConditions_nonempty (N : ℕ) : (finiteLawConditions N).Nonempty := by
  refine ⟨⟨(liftedLaw N).toMeasure, inferInstance⟩, ?_⟩
  intro k hk r
  change ((liftedLaw N).toMeasure (cylinder k r)).toNNReal = _
  rw [liftedLaw_cylinder hk r]

theorem exists_syracuseLimit : ∃ μ : Measure (PadicInt 3), IsSyracuseLimit μ := by
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    finiteLawConditions
    (fun N ν hν k hk r => hν k (hk.trans (Nat.le_succ N)) r)
    finiteLawConditions_nonempty
    (finiteLawConditions_isClosed 0).isCompact
    finiteLawConditions_isClosed
  obtain ⟨ν, hν⟩ := hne
  refine ⟨ν, inferInstance, ?_⟩
  intro n r
  have h := Set.mem_iInter.mp hν n n le_rfl r
  have he := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_toNNReal ((syracuseLaw n).apply_ne_top r)] using he

end SyracuseReport
