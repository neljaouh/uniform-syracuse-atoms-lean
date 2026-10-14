import FiniteTransport

namespace SyracuseReport

/-- Reduction from a finer power-of-three residue group to a coarser one. -/
def residueProjection {q t : ℕ} (h : t ≤ q) : ZMod (3 ^ q) →+* ZMod (3 ^ t) :=
  ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ t))

@[simp] theorem residueProjection_intCast {q t : ℕ} (h : t ≤ q) (M : ℤ) :
    residueProjection h (M : ZMod (3 ^ q)) = (M : ZMod (3 ^ t)) := by
  exact map_intCast (residueProjection h) M

theorem residueProjection_val {q t : ℕ} (h : t ≤ q) (r : ZMod (3 ^ q)) :
    residueProjection h r = ((r.val : ℤ) : ZMod (3 ^ t)) := by
  have hr : ((r.val : ℤ) : ZMod (3 ^ q)) = r := by simp
  calc
    residueProjection h r = residueProjection h ((r.val : ℤ) : ZMod (3 ^ q)) :=
      congrArg (residueProjection h) hr.symm
    _ = _ := residueProjection_intCast h r.val

theorem residueProjection_surjective {q t : ℕ} (h : t ≤ q) :
    Function.Surjective (residueProjection h) := by
  intro z
  refine ⟨((z.val : ℤ) : ZMod (3 ^ q)), ?_⟩
  rw [residueProjection_intCast]
  simp

theorem residueProjection_comp {q t s : ℕ} (hqt : t ≤ q) (hts : s ≤ t)
    (r : ZMod (3 ^ q)) :
    residueProjection hts (residueProjection hqt r) =
      residueProjection (hts.trans hqt) r := by
  have hr : ((r.val : ℤ) : ZMod (3 ^ q)) = r := by simp
  rw [← hr]
  simp only [residueProjection_intCast]

theorem wordTransport_lift (w : Word) {q t : ℕ} (hqt : t ≤ q)
    (h : ZMod (3 ^ t) → ℝ) (M : ℤ) :
    wordTransport w q M (fun z => h (residueProjection hqt z)) =
      wordTransport w t M h := by
  classical
  unfold wordTransport
  split_ifs <;> simp only [residueProjection_intCast]

/-- Exact lifting identity for the finite affine transport. -/
theorem finiteTransport_lift (w : Word) {q t : ℕ} (hqt : t ≤ q)
    (h : ZMod (3 ^ t) → ℝ) (r : ZMod (3 ^ (w.length + q))) :
    finiteTransport w q (fun z => h (residueProjection hqt z)) r =
      finiteTransport w t h (residueProjection (Nat.add_le_add_left hqt w.length) r) := by
  have hr : ((r.val : ℤ) : ZMod (3 ^ (w.length + q))) = r := by simp
  calc
    finiteTransport w q (fun z => h (residueProjection hqt z)) r =
        wordTransport w q r.val (fun z => h (residueProjection hqt z)) := by
      simpa only [hr] using finiteTransport_eq_integer w q
        (fun z => h (residueProjection hqt z)) r.val
    _ = wordTransport w t r.val h := wordTransport_lift w hqt h r.val
    _ = finiteTransport w t h ((r.val : ℤ) : ZMod (3 ^ (w.length + t))) :=
      (finiteTransport_eq_integer w t h r.val).symm
    _ = finiteTransport w t h
        (residueProjection (Nat.add_le_add_left hqt w.length) r) := by
      rw [residueProjection_val]

/-- Lifting preserves every uniform absolute bound, hence the finite L-infinity norm. -/
theorem lift_uniform_bound_iff {q t : ℕ} (hqt : t ≤ q)
    (h : ZMod (3 ^ t) → ℝ) (K : ℝ) :
    (∀ r : ZMod (3 ^ q), |h (residueProjection hqt r)| ≤ K) ↔
      (∀ z : ZMod (3 ^ t), |h z| ≤ K) := by
  constructor
  · intro hf z
    obtain ⟨r, hr⟩ := residueProjection_surjective hqt z
    rw [← hr]
    exact hf r
  · intro hf r
    exact hf (residueProjection hqt r)

end SyracuseReport
