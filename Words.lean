import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-! Concrete positive-integer words, in the outer-first order of the report.
The constructor appends the innermost letter. No arithmetic injectivity
assumption is made: it is proved below for the actual integer numerator. -/

namespace SyracuseReport

inductive Word where
  | nil : Word
  | snoc (initial : Word) (last : ℕ+) : Word
  deriving DecidableEq

namespace Word

/-- Letters in innermost-first order. This gives a simple exact finite-list
encoding of words; all length and total statistics are order-insensitive. -/
def letters : Word → List ℕ+
  | nil => []
  | snoc w a => a :: letters w

def ofReverseList : List ℕ+ → Word
  | [] => nil
  | a :: l => snoc (ofReverseList l) a

@[simp] theorem letters_ofReverseList (l : List ℕ+) :
    letters (ofReverseList l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofReverseList, letters, ih]

@[simp] theorem ofReverseList_letters (w : Word) :
    ofReverseList (letters w) = w := by
  induction w with
  | nil => rfl
  | snoc w a ih => simp [letters, ofReverseList, ih]

theorem ofReverseList_injective : Function.Injective ofReverseList := by
  intro l k h
  simpa only [letters_ofReverseList] using congrArg letters h

def length : Word → ℕ
  | nil => 0
  | snoc w _ => w.length + 1

def total : Word → ℕ
  | nil => 0
  | snoc w a => w.total + (a : ℕ)

/-- The integer `2^A β`, computed without rational division. -/
def numerator : Word → ℕ
  | nil => 0
  | snoc w a => 2 ^ (a : ℕ) * w.numerator + 3 ^ w.length

noncomputable def beta (w : Word) : ℝ := w.numerator / (2 : ℝ) ^ w.total

noncomputable def probability (w : Word) : ℝ := 1 / (2 : ℝ) ^ w.total

noncomputable def coefficient (w : Word) : ℝ :=
  (3 : ℝ) ^ w.length / (2 : ℝ) ^ w.total

def concat (w : Word) : Word → Word
  | nil => w
  | snoc v a => snoc (concat w v) a

@[simp] theorem length_ofReverseList (l : List ℕ+) :
    length (ofReverseList l) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofReverseList, length, ih]

@[simp] theorem total_ofReverseList (l : List ℕ+) :
    total (ofReverseList l) = (l.map (fun a => (a : ℕ))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofReverseList, total, ih, Nat.add_comm]

@[simp] theorem length_nil : length nil = 0 := rfl
@[simp] theorem length_snoc (w : Word) (a : ℕ+) :
    length (snoc w a) = length w + 1 := rfl
@[simp] theorem total_nil : total nil = 0 := rfl
@[simp] theorem total_snoc (w : Word) (a : ℕ+) :
    total (snoc w a) = total w + (a : ℕ) := rfl
@[simp] theorem numerator_nil : numerator nil = 0 := rfl
@[simp] theorem numerator_snoc (w : Word) (a : ℕ+) :
    numerator (snoc w a) = 2 ^ (a : ℕ) * numerator w + 3 ^ length w := rfl

theorem length_eq_zero_iff (w : Word) : w.length = 0 ↔ w = nil := by
  cases w <;> simp

theorem total_pos (w : Word) (hw : w ≠ nil) : 0 < w.total := by
  cases w with
  | nil => exact (hw rfl).elim
  | snoc w a => exact Nat.add_pos_right w.total a.pos

theorem two_pow_mod (a : ℕ) (ha : 0 < a) : 2 ^ a % 2 = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  rw [hk, pow_succ]
  omega

theorem three_pow_mod (d : ℕ) : 3 ^ d % 2 = 1 := by
  induction d with
  | zero => decide
  | succ d ih => simp [pow_succ, Nat.mul_mod, ih]

/-- The nonempty prefix factor in the last-letter recovery is always odd. -/
theorem numerator_odd (w : Word) (hw : w ≠ nil) : w.numerator % 2 = 1 := by
  cases w with
  | nil => exact (hw rfl).elim
  | snoc w a =>
    simp [numerator, Nat.add_mod, Nat.mul_mod, two_pow_mod _ a.pos,
      three_pow_mod]

theorem numerator_pos (w : Word) (hw : w ≠ nil) : 0 < w.numerator := by
  have := numerator_odd w hw
  omega

private theorem exponent_le (i j a b : ℕ) (hb : b % 2 = 1)
    (h : 2 ^ i * a = 2 ^ j * b) : i ≤ j := by
  by_contra hij
  have hji : j ≤ i := by omega
  have hpos : 0 < i - j := by omega
  have he : 2 ^ i = 2 ^ j * 2 ^ (i - j) := by
    rw [← pow_add, Nat.add_sub_of_le hji]
  rw [he, Nat.mul_assoc] at h
  have hab : 2 ^ (i - j) * a = b :=
    Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ j) h
  have hmod : b % 2 = 0 := by
    rw [← hab, Nat.mul_mod, two_pow_mod _ hpos]
    simp
  omega

theorem odd_factor_exponent_unique (i j a b : ℕ)
    (ha : a % 2 = 1) (hb : b % 2 = 1)
    (h : 2 ^ i * a = 2 ^ j * b) : i = j :=
  Nat.le_antisymm (exponent_le i j a b hb h) (exponent_le j i b a ha h.symm)

/-- Lemma `offset-injective`, including the empty and one-letter cases. -/
theorem fixed_total_numerator_injective (w v : Word)
    (hlen : w.length = v.length) (htotal : w.total = v.total)
    (hnum : w.numerator = v.numerator) : w = v := by
  induction w generalizing v with
  | nil =>
    have : v.length = 0 := by simpa using hlen.symm
    exact ((length_eq_zero_iff v).mp this).symm
  | snoc w a ih =>
    cases v with
    | nil => simp at hlen
    | snoc v b =>
      have hl : w.length = v.length := by simpa using hlen
      by_cases hw : w = nil
      · subst w
        have hv : v = nil := (length_eq_zero_iff v).mp (by simpa using hl.symm)
        subst v
        have hab : a = b := by simpa using htotal
        cases hab
        rfl
      · have hv : v ≠ nil := by
          intro hv
          subst v
          exact hw ((length_eq_zero_iff w).mp (by simpa using hl))
        have hp : 2 ^ (a : ℕ) * w.numerator = 2 ^ (b : ℕ) * v.numerator := by
          simp only [numerator_snoc, hl] at hnum
          omega
        have habn : (a : ℕ) = (b : ℕ) :=
          odd_factor_exponent_unique _ _ _ _ (numerator_odd w hw)
            (numerator_odd v hv) hp
        have hab : a = b := Subtype.ext habn
        cases hab
        have ht : w.total = v.total := by simpa using htotal
        have hn : w.numerator = v.numerator :=
          Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (a : ℕ)) hp
        exact congrArg (fun u => snoc u a) (ih v hl ht hn)

theorem coefficient_pos (w : Word) : 0 < w.coefficient := by
  unfold coefficient
  positivity

theorem probability_pos (w : Word) : 0 < w.probability := by
  unfold probability
  positivity

theorem beta_nonneg (w : Word) : 0 ≤ w.beta := by
  unfold beta
  positivity

@[simp] theorem length_concat (w v : Word) : (w.concat v).length = w.length + v.length := by
  induction v with
  | nil => simp [concat]
  | snoc v a ih => simp [concat, ih, Nat.add_assoc]

@[simp] theorem total_concat (w v : Word) : (w.concat v).total = w.total + v.total := by
  induction v with
  | nil => simp [concat]
  | snoc v a ih => simp [concat, ih, Nat.add_assoc]

theorem numerator_concat (w v : Word) :
    (w.concat v).numerator = 2 ^ v.total * w.numerator + 3 ^ w.length * v.numerator := by
  induction v with
  | nil => simp [concat]
  | snoc v a ih =>
    simp only [concat, numerator_snoc, total_snoc, length_concat, ih, pow_add]
    ring

/-- The real coefficient in the report is multiplicative under outer-first concatenation. -/
theorem coefficient_concat (w v : Word) :
    (w.concat v).coefficient = w.coefficient * v.coefficient := by
  simp only [coefficient, length_concat, total_concat, pow_add]
  ring

/-- The offset composition identity in the same word order as the manuscript. -/
theorem beta_concat (w v : Word) :
    (w.concat v).beta = w.beta + w.coefficient * v.beta := by
  have hw : (2 : ℝ) ^ w.total ≠ 0 := by positivity
  have hv : (2 : ℝ) ^ v.total ≠ 0 := by positivity
  simp only [beta, numerator_concat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, total_concat, pow_add, coefficient]
  field_simp

@[simp] theorem probability_concat (w v : Word) :
    (w.concat v).probability = w.probability * v.probability := by
  simp only [probability, total_concat, pow_add]
  ring

@[simp] theorem letters_concat (w v : Word) :
    letters (w.concat v) = letters v ++ letters w := by
  induction v with
  | nil => simp [concat, letters]
  | snoc v a ih => simp [concat, letters, ih]

theorem concat_pair_injective_at_lengths (d b : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1.concat p.2)
      {p | p.1.length = d ∧ p.2.length = b} := by
  rintro ⟨w₁, v₁⟩ ⟨hw₁, hv₁⟩ ⟨w₂, v₂⟩ ⟨hw₂, hv₂⟩ heq
  have hl := congrArg letters heq
  simp only [letters_concat] at hl
  have hvlen₁ : (letters v₁).length = b := by
    rw [← length_ofReverseList (letters v₁), ofReverseList_letters, hv₁]
  have hvlen₂ : (letters v₂).length = b := by
    rw [← length_ofReverseList (letters v₂), ofReverseList_letters, hv₂]
  have hvl : letters v₁ = letters v₂ := by
    have H := congrArg (List.take b) hl
    simpa [hvlen₁, hvlen₂] using H
  have hwl : letters w₁ = letters w₂ := by
    have H := congrArg (List.drop b) hl
    simpa [hvlen₁, hvlen₂] using H
  have hv : v₁ = v₂ := by
    simpa only [ofReverseList_letters] using congrArg ofReverseList hvl
  have hw : w₁ = w₂ := by
    simpa only [ofReverseList_letters] using congrArg ofReverseList hwl
  simp [hw, hv]

/-- The same fixed-total theorem for the real affine offset used in intervals. -/
theorem fixed_total_beta_injective (w v : Word)
    (hlen : w.length = v.length) (htotal : w.total = v.total)
    (hbeta : w.beta = v.beta) : w = v := by
  apply fixed_total_numerator_injective w v hlen htotal
  have hp : (2 : ℝ) ^ v.total ≠ 0 := by positivity
  simp only [beta, htotal] at hbeta
  have hn : (w.numerator : ℝ) = v.numerator := (div_left_inj' hp).mp hbeta
  exact_mod_cast hn

end Word
end SyracuseReport
