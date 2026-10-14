import HaarReference

/-! Ternary cylinders generate the Borel sigma algebra. Consequently their
masses determine a finite measure, in particular any Syracuse limit law.
-/
namespace SyracuseReport
open MeasureTheory

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

def cylinderFamily : Set (Set (PadicInt 3)) :=
  {s | ∃ n : ℕ, ∃ r : ZMod (3 ^ n), s = cylinder n r}

theorem cylinder_centered (n : ℕ) (x : PadicInt 3) :
    cylinder n (PadicInt.toZModPow n x) =
      Metric.closedBall x ((3 : ℝ) ^ (-(n : ℤ))) := by
  have hx : x ∈ cylinder n (PadicInt.toZModPow n x) := rfl
  rw [cylinder_eq_closedBall] at hx ⊢
  exact IsUltrametricDist.closedBall_eq_of_mem hx

theorem cylinderFamily_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis cylinderFamily := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro s ⟨n, r, rfl⟩
    exact (isClopen_cylinder n r).isOpen
  · intro x u hxu hu
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hxu
    obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt 3 hε
    simp only [Nat.cast_ofNat] at hn
    refine ⟨cylinder n (PadicInt.toZModPow n x), ⟨n, _, rfl⟩, rfl, ?_⟩
    intro y hy
    apply hball
    rw [cylinder_centered] at hy
    exact lt_of_le_of_lt hy hn

theorem cylinderFamily_isPiSystem : IsPiSystem cylinderFamily := by
  classical
  rintro s ⟨m, r, rfl⟩ t ⟨n, z, rfl⟩ hne
  rcases le_total m n with hmn | hnm
  · rw [cylinder_inter_of_le hmn] at hne ⊢
    split_ifs at hne ⊢ with h
    · exact ⟨n, z, rfl⟩
    · exact hne.elim (fun _ hx => False.elim hx)
  · rw [Set.inter_comm, cylinder_inter_of_le hnm] at hne ⊢
    split_ifs at hne ⊢ with h
    · exact ⟨m, r, rfl⟩
    · exact hne.elim (fun _ hx => False.elim hx)

theorem borel_eq_generateFrom_cylinders :
    borel (PadicInt 3) = MeasurableSpace.generateFrom cylinderFamily :=
  cylinderFamily_isTopologicalBasis.borel_eq_generateFrom

theorem measure_eq_of_cylinders (μ ν : Measure (PadicInt 3))
    [IsFiniteMeasure μ]
    (hcyl : ∀ n r, μ (cylinder n r) = ν (cylinder n r))
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  apply ext_of_generate_finite cylinderFamily borel_eq_generateFrom_cylinders
    cylinderFamily_isPiSystem
  · rintro s ⟨n, r, rfl⟩
    exact hcyl n r
  · exact huniv

theorem syracuseLimit_unique (μ ν : Measure (PadicInt 3))
    (hμ : IsSyracuseLimit μ) (hν : IsSyracuseLimit ν) : μ = ν := by
  letI := hμ.1
  letI := hν.1
  exact measure_eq_of_cylinders μ ν
    (fun n r => (hμ.2 n r).trans (hν.2 n r).symm)
    (by simp)

theorem additiveHaar_unique (lam : Measure (PadicInt 3))
    (hLam : IsAdditiveHaar lam) : lam = additiveHaar := by
  letI := hLam.1
  exact measure_eq_of_cylinders lam additiveHaar
    (fun n r => (hLam.2 n r).trans (additiveHaar_cylinder n r).symm)
    (by simp)

end SyracuseReport
