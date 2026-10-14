import WordOuter

/-! Summable fixed-length word expansion of the Syracuse density. -/

namespace SyracuseReport

set_option maxHeartbeats 1000000 in

theorem hasSum_fixedLength_density :
    ∀ (d t : ℕ) (M : ℤ),
      HasSum
        (fun w : {w : Word // w.length = d} =>
          wordTransport w.1 t M (density t))
        (density (d + t) (M : ZMod (3 ^ (d + t)))) := by
  intro d
  induction d with
  | zero =>
      intro t M
      rw [Nat.zero_add]
      let f := fun w : {w : Word // w.length = 0} =>
        wordTransport w.1 t M (density t)
      let w0 : {w : Word // w.length = 0} := ⟨Word.nil, rfl⟩
      have hs : HasSum f (f w0) := hasSum_single w0 fun w hw =>
        (hw (Subtype.ext ((Word.length_eq_zero_iff w.1).mp w.2))).elim
      simpa [f, w0] using hs
  | succ d ih =>
      intro t M
      let inner := fun (a : ℕ+) (w : {w : Word // w.length = d}) =>
        wordTransport ((oneLetterWord a).concat w.1) t M (density t)
      let outer := fun a : ℕ+ =>
        wordTransport (oneLetterWord a) (d + t) M (density (d + t))
      have hinner : ∀ a : ℕ+,
          HasSum (inner a) (outer a) := by
        intro a
        by_cases hc : Contributes (oneLetterWord a) M
        · have hscaled := (ih t (inverseInteger (oneLetterWord a) M)).mul_left
            (oneLetterWord a).coefficient
          have hpoint : ∀ w : {w : Word // w.length = d},
              inner a w = (oneLetterWord a).coefficient *
                wordTransport w.1 t (inverseInteger (oneLetterWord a) M) (density t) := by
            intro w
            dsimp [inner]
            rw [wordTransport_concat]
            calc
              wordTransport (oneLetterWord a) (w.1.length + t) M
                  (finiteTransport w.1 t (density t)) =
                  (oneLetterWord a).coefficient *
                    finiteTransport w.1 t (density t)
                      (inverseInteger (oneLetterWord a) M :
                        ZMod (3 ^ (w.1.length + t))) := by
                        unfold wordTransport
                        simp only [hc, ite_true]
              _ = _ := by rw [finiteTransport_eq_integer]
          have hout : outer a = (oneLetterWord a).coefficient *
              density (d + t) (inverseInteger (oneLetterWord a) M :
                ZMod (3 ^ (d + t))) := by
            dsimp [outer]
            unfold wordTransport
            simp only [hc, ite_true]
          rw [hout]
          have hfun : inner a = fun w => (oneLetterWord a).coefficient *
              wordTransport w.1 t (inverseInteger (oneLetterWord a) M) (density t) :=
            funext hpoint
          rw [hfun]
          exact hscaled
        · have hpoint : ∀ w : {w : Word // w.length = d}, inner a w = 0 := by
            intro w
            dsimp [inner]
            rw [wordTransport_concat]
            simp [wordTransport, hc]
          have hout : outer a = 0 := by
            dsimp [outer]
            simp [wordTransport, hc]
          rw [hout]
          have hfun : inner a = fun _ => 0 := funext hpoint
          rw [hfun]
          exact hasSum_zero
      have houter : HasSum outer
          (density ((d + t) + 1) (M : ZMod (3 ^ ((d + t) + 1)))) := by
        simpa only [outer] using hasSum_oneLetter_density_transport (d + t) M
      have hnonneg : 0 ≤ fun p : ℕ+ × {w : Word // w.length = d} =>
          inner p.1 p.2 := by
        intro p
        exact wordTransport_density_nonneg ((oneLetterWord p.1).concat p.2.1) t M
      have hprod : Summable (fun p : ℕ+ × {w : Word // w.length = d} =>
          inner p.1 p.2) := by
        apply (summable_prod_of_nonneg hnonneg).2
        refine ⟨fun a => (hinner a).summable, ?_⟩
        exact houter.summable.congr fun a => (hinner a).tsum_eq.symm
      have hprodSum : HasSum
          (fun p : ℕ+ × {w : Word // w.length = d} => inner p.1 p.2)
          (density ((d + t) + 1) (M : ZMod (3 ^ ((d + t) + 1)))) := by
        have hsumEq :
            (∑' p : ℕ+ × {w : Word // w.length = d}, inner p.1 p.2) =
              density ((d + t) + 1) (M : ZMod (3 ^ ((d + t) + 1))) := by
          rw [hprod.tsum_prod]
          simp_rw [(hinner _).tsum_eq]
          exact houter.tsum_eq
        have hh := hprod.hasSum
        rw [hsumEq] at hh
        exact hh
      have hreindexed : HasSum
          (fun w : {w : Word // w.length = d + 1} =>
            wordTransport w.1 t M (density t))
          (density ((d + t) + 1) (M : ZMod (3 ^ ((d + t) + 1)))) := by
        apply (outerPrependEquiv d).hasSum_iff.mp
        have hfun :
            ((fun w : {w : Word // w.length = d + 1} =>
              wordTransport w.1 t M (density t)) ∘ outerPrependEquiv d) =
              (fun p : ℕ+ × {w : Word // w.length = d} => inner p.1 p.2) := by
          funext p
          rfl
        rw [hfun]
        exact hprodSum
      have hdepth : (d + 1) + t = (d + t) + 1 := by omega
      rw [hdepth]
      exact hreindexed

theorem density_word_decomposition (d t : ℕ) (M : ℤ) :
    density (d + t) (M : ZMod (3 ^ (d + t))) =
      ∑' w : Word,
        if w.length = d then wordTransport w t M (density t) else 0 := by
  have hs := (hasSum_fixedLength_density d t M).tsum_eq
  calc
    density (d + t) (M : ZMod (3 ^ (d + t))) =
        ∑' w : {w : Word // w.length = d},
          wordTransport w.1 t M (density t) := hs.symm
    _ = _ := (tsum_length_eq_subtype d
      (fun w => wordTransport w t M (density t))).symm

end SyracuseReport
