import Words

/-! Elementary integer scale schedule used by the fixed-block construction. -/

namespace SyracuseReport

def baseBlockLength : ℕ := 10 ^ 6

def blockLength : ℕ → ℕ
  | 0 => baseBlockLength
  | j + 1 => blockLength j + blockLength j / 100

def blockIncrement (j : ℕ) : ℕ := blockLength j / 100

def terminalDepth (j : ℕ) : ℕ := blockLength j / 4

@[simp] theorem blockLength_zero : blockLength 0 = baseBlockLength := rfl

@[simp] theorem blockLength_succ (j : ℕ) :
    blockLength (j + 1) = blockLength j + blockIncrement j := rfl

theorem baseBlockLength_eq : baseBlockLength = 1000000 := by norm_num [baseBlockLength]

theorem baseBlockLength_le (j : ℕ) : baseBlockLength ≤ blockLength j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [blockLength_succ]
      omega

theorem blockLength_ge_200 (j : ℕ) : 200 ≤ blockLength j :=
  (by norm_num [baseBlockLength] : 200 ≤ baseBlockLength).trans (baseBlockLength_le j)

theorem blockIncrement_bounds (j : ℕ) :
    blockLength j / 200 ≤ blockIncrement j ∧ blockIncrement j ≤ blockLength j / 100 := by
  unfold blockIncrement
  constructor
  · exact Nat.div_le_div_left (by omega : 100 ≤ 200) (by norm_num)
  · exact le_rfl

theorem blockLength_step_bounds (j : ℕ) :
    blockLength j + blockLength j / 200 ≤ blockLength (j + 1) ∧
      blockLength (j + 1) ≤ blockLength j + blockLength j / 100 := by
  rw [blockLength_succ]
  exact ⟨Nat.add_le_add_left (blockIncrement_bounds j).1 _, le_rfl⟩

theorem terminalDepth_pos (j : ℕ) : 1 ≤ terminalDepth j := by
  unfold terminalDepth
  have := blockLength_ge_200 j
  omega

theorem terminalDepth_lower (j : ℕ) : blockLength j / 8 ≤ terminalDepth j := by
  unfold terminalDepth
  exact Nat.div_le_div_left (by norm_num : 4 ≤ 8) (by norm_num)

theorem terminalDepth_le (j : ℕ) : terminalDepth j ≤ blockLength j := by
  unfold terminalDepth
  exact Nat.div_le_self _ _

end SyracuseReport
