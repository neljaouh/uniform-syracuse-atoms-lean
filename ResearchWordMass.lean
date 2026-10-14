import ResearchWordFibre

/-! The exact mass of a fixed-total slice of the finite Syracuse word law. -/

namespace SyracuseReport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fixed_total_word_mass (d A : ℕ) (R : ℤ) :
    (∑' w : {w : Word // w.length = d},
      if w.1.total = A then
        if Contributes w.1 R then w.1.probability else 0
      else 0) =
      ((fixedTotalContributors d A R).card : ℝ) / (2 : ℝ) ^ A := by
  classical
  let s : Finset Word := fixedTotalContributors d A R
  let liftWord : {w : Word // w ∈ s} → {w : Word // w.length = d} :=
    fun w => ⟨w.1, (mem_fixedTotalContributors_iff d A R w.1).mp w.2 |>.1⟩
  let F : Finset {w : Word // w.length = d} := s.attach.image liftWord
  have hlift : Function.Injective liftWord := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : {w : Word // w.length = d} => z.1) hxy
  have hmem (w : {w : Word // w.length = d})
      (hA : w.1.total = A) (hc : Contributes w.1 R) : w ∈ F := by
    have hs : w.1 ∈ s :=
      (mem_fixedTotalContributors_iff d A R w.1).mpr ⟨w.2, hA, hc⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨w.1, hs⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl
  have hzero (w : {w : Word // w.length = d}) (hw : w ∉ F) :
      (if w.1.total = A then
        if Contributes w.1 R then w.1.probability else 0
      else 0) = 0 := by
    by_cases hA : w.1.total = A
    · by_cases hc : Contributes w.1 R
      · exact False.elim (hw (hmem w hA hc))
      · simp [hA, hc]
    · simp [hA]
  rw [tsum_eq_sum hzero]
  have hFs (w : {w : Word // w.length = d}) (hw : w ∈ F) : w.1 ∈ s := by
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hw
    change liftWord v = w at hv
    have hv' := congrArg Subtype.val hv
    change v.1 = w.1 at hv'
    exact hv' ▸ v.2
  calc
    (∑ w ∈ F,
      if w.1.total = A then
        if Contributes w.1 R then w.1.probability else 0
      else 0) = ∑ w ∈ F, w.1.probability := by
        apply Finset.sum_congr rfl
        intro w hw
        have hs := (mem_fixedTotalContributors_iff d A R w.1).mp (hFs w hw)
        simp [hs.2.1, hs.2.2]
    _ = ∑ w ∈ s, w.probability := by
      dsimp [F]
      rw [Finset.sum_image (fun x _ y _ hxy => hlift hxy)]
      simpa only [liftWord] using (Finset.sum_attach s Word.probability)
    _ = (s.card : ℝ) / (2 : ℝ) ^ A := by
      calc
        _ = ∑ _w ∈ s, (1 / (2 : ℝ) ^ A) := by
          apply Finset.sum_congr rfl
          intro w hw
          have hA := ((mem_fixedTotalContributors_iff d A R w).mp hw).2.1
          simp [Word.probability, hA]
        _ = (s.card : ℝ) / (2 : ℝ) ^ A := by simp [div_eq_mul_inv]

/-- Group the actual finite Syracuse atom by the total valuation of its
words. The right side is a convergent series of nonnegative real terms. -/
theorem finite_syracuse_atom_total_series (d : ℕ) (R : ℤ) :
    HasSum
      (fun A : ℕ =>
        ((fixedTotalContributors d A R).card : ℝ) / (2 : ℝ) ^ A)
      (syracuseLaw d (R : ZMod (3 ^ d))).toReal := by
  classical
  let f : {w : Word // w.length = d} → ℝ :=
    fun w => if Contributes w.1 R then w.1.probability else 0
  have hfnonneg : ∀ w, 0 ≤ f w := by
    intro w
    by_cases hc : Contributes w.1 R
    · simpa [f, hc] using (Word.probability_pos w.1).le
    · simp [f, hc]
  have hfle : ∀ w, f w ≤ w.1.probability := by
    intro w
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact (Word.probability_pos w.1).le
  have hfsum : Summable f :=
    Summable.of_nonneg_of_le hfnonneg hfle
      (hasSum_fixedLength_probability d).summable
  have hgroup := hfsum.hasSum.tsum_fiberwise
    (fun w : {w : Word // w.length = d} => w.1.total)
  have hword : (syracuseLaw d (R : ZMod (3 ^ d))).toReal = ∑' w, f w := by
    exact finite_syracuse_atom_word_sum d R
  rw [← hword] at hgroup
  have hinner (A : ℕ) :
      (∑' w : {u : {w : Word // w.length = d} // u.1.total = A}, f w.1) =
        ((fixedTotalContributors d A R).card : ℝ) / (2 : ℝ) ^ A := by
    calc
      _ = ∑' w : {w : Word // w.length = d},
          Set.indicator {u : {w : Word // w.length = d} | u.1.total = A} f w :=
            tsum_subtype _ _
      _ = ∑' w : {w : Word // w.length = d},
          if w.1.total = A then f w else 0 := by
            apply tsum_congr
            intro w
            by_cases hA : w.1.total = A <;> simp [Set.indicator, hA]
      _ = _ := by simpa only [f] using fixed_total_word_mass d A R
  change HasSum
    (fun A : ℕ =>
      ∑' w : {u : {w : Word // w.length = d} // u.1.total = A}, f w.1)
    (syracuseLaw d (R : ZMod (3 ^ d))).toReal at hgroup
  exact hgroup.congr_fun (fun A => (hinner A).symm)

end SyracuseReport
