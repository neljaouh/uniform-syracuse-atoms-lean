import PaperStatements

/-! Exact linearity and concatenation identities for the selected families. -/
namespace SyracuseReport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem wordTransport_congr_residue (w : Word) (q : ℕ) (M R : ℤ)
    (hMR : (M : ZMod (3 ^ (w.length + q))) = R)
    (f : ZMod (3 ^ q) → ℝ) :
    wordTransport w q M f = wordTransport w q R f := by
  rw [← finiteTransport_eq_integer, ← finiteTransport_eq_integer, hMR]

theorem wordTransport_sub (w : Word) (q : ℕ) (M : ℤ)
    (f g : ZMod (3 ^ q) → ℝ) :
    wordTransport w q M (fun z => f z - g z) =
      wordTransport w q M f - wordTransport w q M g := by
  classical
  unfold wordTransport
  split_ifs <;> ring

theorem wordTransport_finset_sum {I : Type*} (s : Finset I)
    (w : Word) (q : ℕ) (M : ℤ) (f : I → ZMod (3 ^ q) → ℝ) :
    wordTransport w q M (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, wordTransport w q M (f i) := by
  classical
  unfold wordTransport
  split_ifs <;> simp [Finset.mul_sum]

theorem wordTransport_concat_integer (w v : Word) (q : ℕ) (M : ℤ)
    (f : ZMod (3 ^ q) → ℝ) :
    wordTransport (w.concat v) q M f =
      if Contributes w M then
        w.coefficient * wordTransport v q (inverseInteger w M) f else 0 := by
  classical
  rw [wordTransport_concat]
  change (if Contributes w M then w.coefficient *
    finiteTransport v q f (inverseInteger w M : ZMod (3 ^ (v.length + q))) else 0) = _
  rw [finiteTransport_eq_integer]

theorem familyTransport_sub (s : Finset Word) (d q : ℕ)
    (f g : ZMod (3 ^ q) → ℝ) (r : ZMod (3 ^ (d + q))) :
    familyTransport s d q (fun z => f z - g z) r =
      familyTransport s d q f r - familyTransport s d q g r := by
  classical
  unfold familyTransport
  simp_rw [wordTransport_sub]
  rw [Finset.sum_sub_distrib]

theorem familyTransport_lift (s : Finset Word) (d : ℕ) {q t : ℕ}
    (hlen : ∀ w ∈ s, w.length = d)
    (hqt : t ≤ q) (f : ZMod (3 ^ t) → ℝ) (r : ZMod (3 ^ (d + q))) :
    familyTransport s d q (fun z => f (residueProjection hqt z)) r =
      familyTransport s d t f (residueProjection (Nat.add_le_add_left hqt d) r) := by
  classical
  unfold familyTransport
  apply Finset.sum_congr rfl
  intro w hw
  rw [wordTransport_lift]
  apply wordTransport_congr_residue
  rw [hlen w hw]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  simpa only [Int.cast_natCast] using (residueProjection_val _ r).symm

theorem selectedPrefixes_transport_concat (N q : ℕ) (M : ℤ)
    (f : ZMod (3 ^ q) → ℝ) :
    (∑ w ∈ selectedPrefixes (N + 1), wordTransport w q M f) =
      ∑ w ∈ selectedPrefixes N,
        wordTransport w (blockLength N + q) M
          (familyTransport (selectedBlock N) (blockLength N) q f) := by
  classical
  rw [selectedPrefixes_succ, Finset.sum_image (selectedPrefix_concat_injective N),
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w hw
  change (∑ v ∈ selectedBlock N, wordTransport (w.concat v) q M f) =
    wordTransport w (blockLength N + q) M
      (fun r => ∑ v ∈ selectedBlock N, wordTransport v q r.val f)
  rw [wordTransport_finset_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [wordTransport_concat_integer]
  change _ = if Contributes w M then w.coefficient *
    wordTransport v q
      ((inverseInteger w M : ZMod (3 ^ (blockLength N + q))).val : ℤ) f else 0
  split_ifs
  · congr 1
    apply wordTransport_congr_residue
    rw [selectedBlock_length hv]
    simp
  · rfl

end SyracuseReport
