import MainStatements
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-! Topological and measurable cylinder facts for the limiting-measure proof.
All cylinders are clopen balls. Their reductions compose exactly, so
intersections can be reduced to the finer finite quotient.
-/
namespace SyracuseReport

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

theorem cylinder_eq_closedBall (n : ℕ) (r : ZMod (3 ^ n)) :
    cylinder n r = Metric.closedBall (r.val : PadicInt 3) ((3 : ℝ) ^ (-(n : ℤ))) := by
  ext x
  change PadicInt.toZModPow n x = r ↔
    dist x (r.val : PadicInt 3) ≤ (3 : ℝ) ^ (-(n : ℤ))
  have hnorm := PadicInt.norm_le_pow_iff_mem_span_pow (p := 3)
    (x - (r.val : PadicInt 3)) n
  simp only [Nat.cast_ofNat] at hnorm
  have hker := PadicInt.ker_toZModPow (p := 3) n
  simp only [Nat.cast_ofNat] at hker
  rw [dist_eq_norm, hnorm,
    ← hker, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_eq_zero]

theorem isClopen_cylinder (n : ℕ) (r : ZMod (3 ^ n)) :
    IsClopen (cylinder n r) := by
  rw [cylinder_eq_closedBall]
  exact IsUltrametricDist.isClopen_closedBall _ (by positivity)

theorem measurableSet_cylinder (n : ℕ) (r : ZMod (3 ^ n)) :
    MeasurableSet (cylinder n r) :=
  (isClopen_cylinder n r).isClosed.measurableSet

theorem padic_reduction_comp {m n : ℕ} (hmn : m ≤ n) (x : PadicInt 3) :
    residueProjection hmn (PadicInt.toZModPow n x) = PadicInt.toZModPow m x := by
  have h := congrArg (fun f : PadicInt 3 →+* ZMod (3 ^ m) => f x)
    (PadicInt.zmod_cast_comp_toZModPow m n hmn)
  exact h

theorem cylinder_inter_of_le {m n : ℕ} (hmn : m ≤ n)
    (r : ZMod (3 ^ m)) (s : ZMod (3 ^ n)) :
    cylinder m r ∩ cylinder n s =
      if residueProjection hmn s = r then cylinder n s else ∅ := by
  classical
  by_cases h : residueProjection hmn s = r
  · rw [if_pos h]
    apply Set.inter_eq_right.mpr
    intro x hx
    change PadicInt.toZModPow n x = s at hx
    change PadicInt.toZModPow m x = r
    rw [← padic_reduction_comp hmn x, hx, h]
  · rw [if_neg h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hy⟩
    change PadicInt.toZModPow m x = r at hx
    change PadicInt.toZModPow n x = s at hy
    exact h (by rw [← hy, padic_reduction_comp, hx])

end SyracuseReport
