import SelectedAffineBounds
import PaperStatements

/-! The finite residue estimate for the manuscript's selected prefix family. -/

namespace SyracuseReport

theorem prefixWindow_real_bound (N : ℕ) :
    (prefixWindow N : ℝ) ≤ 2 * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) := by
  induction N with
  | zero => simp [prefixWindow]
  | succ N ih =>
      have hb := blockWindow_real_le_two_rpow N
      have hmono : (blockLength N : ℝ) ^ (3 / 5 : ℝ) ≤
          (blockLength (N + 1) : ℝ) ^ (3 / 5 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast blockLength_strictMono.monotone (Nat.le_succ N)
        · norm_num
      rw [prefixWindow, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hn : (0 : ℝ) ≤ N := by positivity
      have hmul := mul_le_mul_of_nonneg_left hmono
        (show 0 ≤ 2 * (N : ℝ) by positivity)
      nlinarith

theorem selectedPrefixes_total_image_card_real (N : ℕ) :
    (((selectedPrefixes N).image Word.total).card : ℝ) ≤
      4 * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1 := by
  have hcard : (((selectedPrefixes N).image Word.total).card : ℝ) ≤
      2 * prefixWindow N + 1 := by exact_mod_cast selectedPrefixes_total_image_card N
  have hw := prefixWindow_real_bound N
  linarith

theorem selectedPrefixes_coefficient_bound {N : ℕ} {w : Word}
    (hw : w ∈ selectedPrefixes N) :
    w.coefficient ≤ (16 : ℝ) ^ baseBlockLength / (16 : ℝ) ^ blockLength N := by
  exact (le_div_iff₀ (by positivity)).mpr (selectedPrefixes_coefficient_scaled hw)

theorem selectedPrefixes_scaled_coefficient_bound (N q : ℕ)
    (hq : q ≤ 2 * blockLength N) :
    (3 ^ q : ℕ) * ((16 : ℝ) ^ baseBlockLength / (16 : ℝ) ^ blockLength N) ≤
      (16 : ℝ) ^ baseBlockLength := by
  have hp : (3 : ℝ) ^ q ≤ (16 : ℝ) ^ blockLength N := by
    calc
      (3 : ℝ) ^ q ≤ (3 : ℝ) ^ (2 * blockLength N) :=
        pow_le_pow_right₀ (by norm_num) hq
      _ = (9 : ℝ) ^ blockLength N := by rw [pow_mul]; norm_num
      _ ≤ (16 : ℝ) ^ blockLength N := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (3 : ℝ) ^ q * (16 ^ baseBlockLength / 16 ^ blockLength N) ≤
        16 ^ blockLength N * (16 ^ baseBlockLength / 16 ^ blockLength N) := by
          exact mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (16 : ℝ) ^ baseBlockLength := by field_simp

theorem paper_lem_kernel_bound : PaperStatements.lem_kernel_bound := by
  intro N q hq hqN f
  have hbase := paper_lem_residue_count (selectedPrefixes N) (prefixDepth N) q
    ((2 : ℝ) ^ (baseBlockLength + 1))
    ((16 : ℝ) ^ baseBlockLength / (16 : ℝ) ^ blockLength N)
    hq (fun _ hw => selectedPrefixes_length hw)
    (fun _ hw => selectedPrefixes_beta_bound hw)
    (fun _ hw => selectedPrefixes_coefficient_bound hw) f
  have hcard := selectedPrefixes_total_image_card_real N
  have hc := selectedPrefixes_scaled_coefficient_bound N q hqN
  have hmean : 0 ≤ finiteMean (fun x => |f x|) := by
    unfold finiteMean
    exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  calc
    ‖familyTransport (selectedPrefixes N) (prefixDepth N) q f‖ ≤
        (((selectedPrefixes N).image Word.total).card : ℝ) *
          ((2 : ℝ) ^ (baseBlockLength + 1) +
            (3 ^ q : ℕ) * (16 ^ baseBlockLength / 16 ^ blockLength N)) *
              finiteMean (fun x => |f x|) := hbase
    _ ≤ (4 * N * (blockLength N : ℝ) ^ (3 / 5 : ℝ) + 1) *
          ((2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength) *
            finiteMean (fun x => |f x|) := by
              gcongr

end SyracuseReport
