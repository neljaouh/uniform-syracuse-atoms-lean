import BlockFamilies

/-! Real geometric bounds for the actual integer block schedule. -/

namespace SyracuseReport
open scoped BigOperators

theorem blockIncrement_real_bounds (j : ℕ) :
    (blockLength j : ℝ) / 200 ≤ (blockIncrement j : ℝ) ∧
      (blockIncrement j : ℝ) ≤ (blockLength j : ℝ) / 100 := by
  have hb := blockLength_ge_200 j
  have hr : blockLength j % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have he : 2 ≤ blockLength j / 100 := by omega
  have hdecomp := Nat.mod_add_div (blockLength j) 100
  have hdecompR : ((blockLength j % 100 : ℕ) : ℝ) +
      100 * (blockIncrement j : ℝ) = (blockLength j : ℝ) := by
    exact_mod_cast hdecomp
  have hrR : ((blockLength j % 100 : ℕ) : ℝ) < 100 := by exact_mod_cast hr
  have heR : (2 : ℝ) ≤ blockIncrement j := by exact_mod_cast he
  have hnR : (0 : ℝ) ≤ ((blockLength j % 100 : ℕ) : ℝ) := by positivity
  constructor <;> nlinarith

theorem blockLength_real_step_bounds (j : ℕ) :
    (201 / 200 : ℝ) * blockLength j ≤ (blockLength (j + 1) : ℝ) ∧
      (blockLength (j + 1) : ℝ) ≤ (101 / 100 : ℝ) * blockLength j := by
  have h := blockIncrement_real_bounds j
  have he : (blockLength (j + 1) : ℝ) = blockLength j + blockIncrement j := by
    rw [blockLength_succ, Nat.cast_add]
  constructor <;> nlinarith

theorem blockLength_geometric_bounds (j : ℕ) :
    (baseBlockLength : ℝ) * (201 / 200 : ℝ) ^ j ≤ (blockLength j : ℝ) ∧
      (blockLength j : ℝ) ≤ (baseBlockLength : ℝ) * (101 / 100 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hs := blockLength_real_step_bounds j
      constructor
      · calc
          (baseBlockLength : ℝ) * (201 / 200 : ℝ) ^ (j + 1) =
              (201 / 200 : ℝ) * (baseBlockLength * (201 / 200 : ℝ) ^ j) := by
                rw [pow_succ]
                ring
          _ ≤ (201 / 200 : ℝ) * blockLength j :=
            mul_le_mul_of_nonneg_left ih.1 (by norm_num)
          _ ≤ _ := hs.1
      · calc
          (blockLength (j + 1) : ℝ) ≤ (101 / 100 : ℝ) * blockLength j := hs.2
          _ ≤ (101 / 100 : ℝ) * (baseBlockLength * (101 / 100 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ = _ := by rw [pow_succ]; ring

theorem blockLength_strictMono : StrictMono blockLength := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hb := blockLength_ge_200 j
  rw [blockLength_succ]
  unfold blockIncrement
  omega

theorem terminalDepth_monotone : Monotone terminalDepth := by
  intro i j hij
  exact Nat.div_le_div_right (blockLength_strictMono.monotone hij)

theorem terminalDepth_real_bounds (j : ℕ) :
    (blockLength j : ℝ) / 8 ≤ (terminalDepth j : ℝ) ∧
      (terminalDepth j : ℝ) ≤ (blockLength j : ℝ) / 4 := by
  have hb := blockLength_ge_200 j
  have hr : blockLength j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have he : 2 ≤ blockLength j / 4 := by omega
  have hdecomp := Nat.mod_add_div (blockLength j) 4
  have hdecompR : ((blockLength j % 4 : ℕ) : ℝ) +
      4 * (terminalDepth j : ℝ) = (blockLength j : ℝ) := by
    exact_mod_cast hdecomp
  have hrR : ((blockLength j % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hr
  have heR : (2 : ℝ) ≤ terminalDepth j := by exact_mod_cast he
  have hnR : (0 : ℝ) ≤ ((blockLength j % 4 : ℕ) : ℝ) := by positivity
  constructor <;> nlinarith

theorem nextBlockDepth_bounds (j : ℕ) :
    terminalDepth j ≤ blockLength j + terminalDepth (j + 1) ∧
      ((blockLength j + terminalDepth (j + 1) : ℕ) : ℝ) ≤
        (501 / 400 : ℝ) * blockLength j := by
  constructor
  · exact (terminalDepth_monotone (Nat.le_succ j)).trans (Nat.le_add_left _ _)
  · have ht := (terminalDepth_real_bounds (j + 1)).2
    have hb := (blockLength_real_step_bounds j).2
    rw [Nat.cast_add]
    nlinarith

theorem prefixDepth_eq_sum (N : ℕ) :
    prefixDepth N = ∑ j ∈ Finset.range N, blockLength j := by
  induction N with
  | zero => simp [prefixDepth]
  | succ N ih => rw [prefixDepth, Finset.sum_range_succ, ih]

theorem prefixDepth_lower (N : ℕ) : N * baseBlockLength ≤ prefixDepth N := by
  induction N with
  | zero => simp [prefixDepth]
  | succ N ih =>
      have hb := baseBlockLength_le N
      rw [prefixDepth, Nat.succ_mul]
      omega

end SyracuseReport
