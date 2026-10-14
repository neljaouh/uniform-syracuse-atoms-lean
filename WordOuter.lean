import TransportLaw

/-! Decomposition of a nonempty word into its outermost letter and tail. -/

namespace SyracuseReport

@[simp] theorem Word.length_letters (w : Word) : w.letters.length = w.length := by
  have h := Word.length_ofReverseList (Word.letters w)
  rw [Word.ofReverseList_letters] at h
  exact h.symm

def prependAtLength (d : ℕ) :
    ℕ+ × {w : Word // w.length = d} → {w : Word // w.length = d + 1}
  | ⟨a, w⟩ => ⟨(oneLetterWord a).concat w.1, by
      rw [Word.length_concat, oneLetterWord_length, w.2]
      omega⟩

theorem prependAtLength_injective (d : ℕ) : Function.Injective (prependAtLength d) := by
  rintro ⟨a, v⟩ ⟨b, w⟩ h
  have hword : (oneLetterWord a).concat v.1 = (oneLetterWord b).concat w.1 :=
    congrArg Subtype.val h
  have hpairs := Word.concat_pair_injective_at_lengths 1 d
    (show (oneLetterWord a, v.1) ∈
      {p : Word × Word | p.1.length = 1 ∧ p.2.length = d} from
        ⟨oneLetterWord_length a, v.2⟩)
    (show (oneLetterWord b, w.1) ∈
      {p : Word × Word | p.1.length = 1 ∧ p.2.length = d} from
        ⟨oneLetterWord_length b, w.2⟩)
    hword
  have hab : a = b := by
    have hone := congrArg Prod.fst hpairs
    have hletters := congrArg Word.letters hone
    simpa [oneLetterWord, Word.letters] using hletters
  have hvw : v = w := by
    apply Subtype.ext
    exact congrArg Prod.snd hpairs
  cases hab
  cases hvw
  rfl

theorem prependAtLength_surjective (d : ℕ) : Function.Surjective (prependAtLength d) := by
  intro W
  let l : List ℕ+ := W.1.letters
  have hlenl : l.length = d + 1 := by
    dsimp [l]
    rw [Word.length_letters, W.2]
  have hne : l ≠ [] := by
    intro he
    rw [he] at hlenl
    simp at hlenl
  let a : ℕ+ := l.getLast hne
  let vword : Word := Word.ofReverseList l.dropLast
  have hvlen : vword.length = d := by
    dsimp [vword]
    rw [Word.length_ofReverseList, List.length_dropLast, hlenl]
    omega
  let v : {w : Word // w.length = d} := ⟨vword, hvlen⟩
  refine ⟨⟨a, v⟩, ?_⟩
  apply Subtype.ext
  change (oneLetterWord a).concat vword = W.1
  have hletters : Word.letters ((oneLetterWord a).concat vword) = W.1.letters := by
    simp only [Word.letters_concat]
    dsimp [vword, a]
    simp only [Word.letters_ofReverseList]
    change l.dropLast ++ [l.getLast hne] = l
    exact List.dropLast_append_getLast hne
  have hword := congrArg Word.ofReverseList hletters
  simpa only [Word.ofReverseList_letters] using hword

noncomputable def outerPrependEquiv (d : ℕ) :
    ℕ+ × {w : Word // w.length = d} ≃ {w : Word // w.length = d + 1} :=
  Equiv.ofBijective (prependAtLength d)
    ⟨prependAtLength_injective d, prependAtLength_surjective d⟩

theorem tsum_length_eq_subtype (d : ℕ) (F : Word → ℝ) :
    (∑' w : Word, if w.length = d then F w else 0) =
      ∑' w : {w : Word // w.length = d}, F w.1 := by
  calc
    _ = ∑' w : Word, ({w : Word | w.length = d}.indicator F) w := by
      apply tsum_congr
      intro w
      by_cases hw : w.length = d
      · simp [Set.indicator, hw]
      · simp [Set.indicator, hw]
    _ = _ := (tsum_subtype {w : Word | w.length = d} F).symm

theorem tsum_fixedLength_succ_reindex (d : ℕ) (F : Word → ℝ) :
    (∑' w : {w : Word // w.length = d + 1}, F w.1) =
      ∑' p : ℕ+ × {w : Word // w.length = d},
        F ((prependAtLength d p).1) := by
  exact ((outerPrependEquiv d).tsum_eq (fun w => F w.1)).symm

end SyracuseReport
