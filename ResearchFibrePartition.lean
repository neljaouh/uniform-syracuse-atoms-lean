import ResearchWeightedCauchy
import ResearchMixedSecond

/-! A word occurs in at most one total/residue fibre.  Consequently the
sum of all finite fibre costs is bounded by the full word expectation. -/

namespace SyracuseReport
open scoped BigOperators

theorem contributes_residue_unique (w : Word) (n : ℕ) (hw : w.length = n)
    (r s : ZMod (3 ^ n))
    (hr : Contributes w (r.val : ℤ))
    (hs : Contributes w (s.val : ℤ)) : r = s := by
  subst n
  have h1 := (wordMap_inverse_fiber w 0 0 (r.val : ℤ)).mpr
    ⟨hr, by change (_ : ZMod 1) = 0; exact Subsingleton.elim _ _⟩
  have h2 := (wordMap_inverse_fiber w 0 0 (s.val : ℤ)).mpr
    ⟨hs, by change (_ : ZMod 1) = 0; exact Subsingleton.elim _ _⟩
  have h := h1.symm.trans h2
  simpa using h

/-- This estimate accounts for every residue and total simultaneously;
there is no multiplicity factor for either index. -/
theorem finite_fibre_weight_sum_le (n N : ℕ) (g : Word → ℝ)
    (hg : ∀ w, 0 ≤ g w)
    (hsum : Summable (fun w : {w : Word // w.length = n} => g w.1)) :
    (∑ r : ZMod (3 ^ n), ∑ A ∈ Finset.Ico n N,
      ∑ w ∈ fixedTotalContributors n A (r.val : ℤ), g w) ≤
        ∑' w : {w : Word // w.length = n}, g w.1 := by
  classical
  let S : Finset (Σ _r : ZMod (3 ^ n), Σ _A : ℕ, Word) :=
    Finset.univ.sigma (fun r =>
      (Finset.Ico n N).sigma (fun A => fixedTotalContributors n A (r.val : ℤ)))
  have hmem (p : {p // p ∈ S}) :
      p.1.2.2.length = n ∧ p.1.2.2.total = p.1.2.1 ∧
        Contributes p.1.2.2 (p.1.1.val : ℤ) := by
    have h := (Finset.mem_sigma.mp (Finset.mem_sigma.mp p.2).2).2
    exact (mem_fixedTotalContributors_iff _ _ _ _).mp h
  let f : {p // p ∈ S} → {w : Word // w.length = n} :=
    fun p => ⟨p.1.2.2, (hmem p).1⟩
  have hf : Function.Injective f := by
    intro p q heq
    have hw : p.1.2.2 = q.1.2.2 := congrArg Subtype.val heq
    have hA : p.1.2.1 = q.1.2.1 := by
      rw [← (hmem p).2.1, ← (hmem q).2.1, hw]
    have hr : p.1.1 = q.1.1 := contributes_residue_unique
      p.1.2.2 n (hmem p).1 p.1.1 q.1.1 (hmem p).2.2
      (by rw [hw]; exact (hmem q).2.2)
    apply Subtype.ext
    rcases p with ⟨⟨r, A, w⟩, hp⟩
    rcases q with ⟨⟨s, B, v⟩, hq⟩
    dsimp at hw hA hr
    subst s
    subst B
    subst v
    rfl
  have hbound := hsum.sum_le_tsum (S.attach.image f) (fun w _ => hg w.1)
  have heq : (∑ w ∈ S.attach.image f, g w.1) =
      ∑ r : ZMod (3 ^ n), ∑ A ∈ Finset.Ico n N,
        ∑ w ∈ fixedTotalContributors n A (r.val : ℤ), g w := by
    rw [Finset.sum_image (fun p _ q _ h => hf h)]
    change (∑ p ∈ S.attach, g p.1.2.2) = _
    rw [Finset.sum_attach S (fun p => g p.2.2)]
    dsimp [S]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_sigma]
  rw [heq] at hbound
  exact hbound

end SyracuseReport
