import BlockGrowth
import BlockWindowBounds

/-! Affine estimates for the actual selected words and concatenated prefixes. -/

namespace SyracuseReport

namespace Word

theorem beta_snoc_formula (w : Word) (a : ℕ+) :
    (w.snoc a).beta = w.beta + w.coefficient / (2 : ℝ) ^ (a : ℕ) := by
  simp only [beta, coefficient, numerator_snoc, total_snoc, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp

theorem coefficient_snoc_formula (w : Word) (a : ℕ+) :
    (w.snoc a).coefficient = 3 * w.coefficient / (2 : ℝ) ^ (a : ℕ) := by
  simp only [coefficient, length_snoc, total_snoc, pow_add, pow_one]
  ring

theorem beta_add_coefficient_le_two_pow (w : Word) :
    w.beta + w.coefficient ≤ (2 : ℝ) ^ w.length := by
  induction w with
  | nil => norm_num [beta, coefficient]
  | snoc w a ih =>
      have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (a : ℕ) := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) a.pos)
      have hc := w.coefficient_pos
      have hb := w.beta_nonneg
      have hd : 4 * w.coefficient / (2 : ℝ) ^ (a : ℕ) ≤
          2 * w.coefficient := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      rw [beta_snoc_formula, coefficient_snoc_formula, length_snoc, pow_succ]
      have heq : w.beta + w.coefficient / (2 : ℝ) ^ (a : ℕ) +
          3 * w.coefficient / (2 : ℝ) ^ (a : ℕ) =
          w.beta + 4 * w.coefficient / (2 : ℝ) ^ (a : ℕ) := by ring
      rw [heq]
      nlinarith

theorem beta_le_two_pow_length (w : Word) : w.beta ≤ (2 : ℝ) ^ w.length := by
  have h := beta_add_coefficient_le_two_pow w
  have hpos := w.coefficient_pos
  linarith

end Word

theorem blockWindow_mul_ten_le (j : ℕ) : 10 * blockWindow j ≤ blockLength j := by
  have h := blockWindow_real_le_tenth j
  have hr : (10 : ℝ) * blockWindow j ≤ (blockLength j : ℝ) := by linarith
  exact_mod_cast hr

theorem selectedBlock_coefficient_scaled {j : ℕ} {w : Word}
    (hw : w ∈ selectedBlock j) :
    w.coefficient * (16 : ℝ) ^ blockIncrement j ≤ 1 := by
  have hlen := selectedBlock_length hw
  have htotal := (selectedBlock_total_bounds hw).1
  have hm := blockWindow_mul_ten_le j
  have he : 100 * blockIncrement j ≤ blockLength j := by
    unfold blockIncrement
    exact Nat.mul_div_le _ _
  have hA : 190 * blockLength j ≤ 100 * w.total := by omega
  have hnum : (3 : ℝ) ^ (w.length * 100) *
      (16 : ℝ) ^ (blockIncrement j * 100) ≤ (2 : ℝ) ^ (w.total * 100) := by
    rw [hlen]
    calc
      (3 : ℝ) ^ (blockLength j * 100) * (16 : ℝ) ^ (blockIncrement j * 100)
          ≤ (3 : ℝ) ^ (blockLength j * 100) * (16 : ℝ) ^ blockLength j := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16)
                (show blockIncrement j * 100 ≤ blockLength j by omega)) (by positivity)
      _ = ((3 : ℝ) ^ 100 * 16) ^ blockLength j := by
            rw [mul_pow, ← pow_mul]
            congr 1
            congr 1
            omega
      _ ≤ ((2 : ℝ) ^ 190) ^ blockLength j :=
            pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ ≤ (2 : ℝ) ^ (w.total * 100) := by
            rw [← pow_mul]
            exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              (show 190 * blockLength j ≤ w.total * 100 by omega)
  apply (pow_le_pow_iff_left₀
    (mul_nonneg w.coefficient_pos.le (by positivity)) (by norm_num : (0 : ℝ) ≤ 1)
    (by decide : (100 : ℕ) ≠ 0)).mp
  simp only [one_pow, mul_pow, Word.coefficient, div_pow, ← pow_mul]
  rw [div_mul_eq_mul_div]
  exact (div_le_one (by positivity)).mpr hnum

theorem blockIncrement_pos (j : ℕ) : 1 ≤ blockIncrement j := by
  have h := blockLength_ge_200 j
  unfold blockIncrement
  omega

theorem selectedBlock_terminal_budget {j : ℕ} {w : Word}
    (hw : w ∈ selectedBlock j) :
    w.coefficient * (2 : ℝ) ^ (blockLength (j + 1) + 1) ≤
      (2 : ℝ) ^ blockLength j := by
  have hs := selectedBlock_coefficient_scaled hw
  have he := blockIncrement_pos j
  have hpow : (2 : ℝ) ^ (blockLength (j + 1) + 1) ≤
      (2 : ℝ) ^ blockLength j * (16 : ℝ) ^ blockIncrement j := by
    rw [blockLength_succ]
    have h16 : (16 : ℝ) ^ blockIncrement j = (2 : ℝ) ^ (4 * blockIncrement j) := by
      rw [pow_mul]
      norm_num
    rw [h16, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show blockLength j + blockIncrement j + 1 ≤
        blockLength j + 4 * blockIncrement j by omega)
  calc
    w.coefficient * (2 : ℝ) ^ (blockLength (j + 1) + 1) ≤
        w.coefficient * ((2 : ℝ) ^ blockLength j * (16 : ℝ) ^ blockIncrement j) :=
      mul_le_mul_of_nonneg_left hpow w.coefficient_pos.le
    _ = (2 : ℝ) ^ blockLength j * (w.coefficient * (16 : ℝ) ^ blockIncrement j) := by ring
    _ ≤ (2 : ℝ) ^ blockLength j := by nlinarith [show 0 < (2 : ℝ) ^ blockLength j by positivity]

theorem selectedPrefixes_affine_budget {N : ℕ} {w : Word}
    (hw : w ∈ selectedPrefixes N) :
    w.beta + w.coefficient * (2 : ℝ) ^ (blockLength N + 1) ≤
      (2 : ℝ) ^ (baseBlockLength + 1) := by
  classical
  induction N generalizing w with
  | zero =>
      simp only [selectedPrefixes_zero, Finset.mem_singleton] at hw
      subst w
      simp [Word.beta, Word.coefficient]
  | succ N ih =>
      rw [selectedPrefixes_succ] at hw
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      have hi := ih hu
      have hb : v.beta ≤ (2 : ℝ) ^ blockLength N := by
        simpa only [selectedBlock_length hv] using v.beta_le_two_pow_length
      have ht := selectedBlock_terminal_budget hv
      have hc := u.coefficient_pos
      have htwo : (2 : ℝ) ^ (blockLength N + 1) =
          (2 : ℝ) ^ blockLength N + (2 : ℝ) ^ blockLength N := by
        rw [pow_succ]
        ring
      have hh : v.beta + v.coefficient * (2 : ℝ) ^ (blockLength (N + 1) + 1) ≤
          (2 : ℝ) ^ (blockLength N + 1) := by
        rw [htwo]
        exact add_le_add hb ht
      rw [Word.beta_concat, Word.coefficient_concat]
      nlinarith

theorem selectedPrefixes_beta_bound {N : ℕ} {w : Word}
    (hw : w ∈ selectedPrefixes N) : w.beta ≤ (2 : ℝ) ^ (baseBlockLength + 1) := by
  have h := selectedPrefixes_affine_budget hw
  have hp : 0 ≤ w.coefficient * (2 : ℝ) ^ (blockLength N + 1) :=
    mul_nonneg w.coefficient_pos.le (by positivity)
  linarith

theorem selectedPrefixes_coefficient_scaled {N : ℕ} {w : Word}
    (hw : w ∈ selectedPrefixes N) :
    w.coefficient * (16 : ℝ) ^ blockLength N ≤ (16 : ℝ) ^ baseBlockLength := by
  classical
  induction N generalizing w with
  | zero =>
      simp only [selectedPrefixes_zero, Finset.mem_singleton] at hw
      subst w
      simp [Word.coefficient]
  | succ N ih =>
      rw [selectedPrefixes_succ] at hw
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      have hi := ih hu
      have hv := selectedBlock_coefficient_scaled hv
      rw [Word.coefficient_concat, blockLength_succ, pow_add]
      calc
        u.coefficient * v.coefficient * ((16 : ℝ) ^ blockLength N * 16 ^ blockIncrement N)
            = (u.coefficient * 16 ^ blockLength N) *
                (v.coefficient * 16 ^ blockIncrement N) := by ring
        _ ≤ (u.coefficient * 16 ^ blockLength N) * 1 := by
              exact mul_le_mul_of_nonneg_left hv (mul_nonneg u.coefficient_pos.le (by positivity))
        _ ≤ (16 : ℝ) ^ baseBlockLength := by simpa using hi

end SyracuseReport
