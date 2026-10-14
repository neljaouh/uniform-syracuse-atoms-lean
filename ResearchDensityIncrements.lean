import ResearchExplicitCollision
import MixingBridge

/-! Quantitative L1 and L2 estimates for successive actual Haar densities.
These are the two inputs to the subcritical interpolation argument. -/
namespace SyracuseReport
open MeasureTheory
open scoped BigOperators

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)
local instance : BorelSpace (PadicInt 3) := ⟨rfl⟩

noncomputable def densityIncrement (n : ℕ) (x : PadicInt 3) : ℝ :=
  cylinderFunction (n + 1) (density (n + 1)) x - cylinderFunction n (density n) x

theorem integrable_densityIncrement_sq (n : ℕ) :
    Integrable (fun x => densityIncrement n x ^ 2) unitHaar := by
  let f := cylinderFunction (n + 1) (density (n + 1))
  let g := cylinderFunction n (density n)
  have hf : Integrable (fun x => f x ^ 2) unitHaar :=
    integrable_cylinderFunction unitHaar (n + 1) (fun r => density (n + 1) r ^ 2)
  have hg : Integrable (fun x => g x ^ 2) unitHaar :=
    integrable_cylinderFunction unitHaar n (fun r => density n r ^ 2)
  have hfg : Integrable (fun x => f x * g x) unitHaar :=
    integrable_mul_cylinderFunction g (integrable_cylinderFunction unitHaar n (density n))
      (n + 1) (density (n + 1))
  have h := (hf.sub (hfg.const_mul 2)).add hg
  apply h.congr
  exact Filter.Eventually.of_forall (fun x => by
    change (f x ^ 2 - 2 * (f x * g x)) + g x ^ 2 = (f x - g x) ^ 2
    ring)

theorem densityIncrement_L2_sq_le (n : ℕ) (hn : 1 ≤ n) :
    (∫ x, densityIncrement n x ^ 2 ∂unitHaar) ≤ 80 * (n : ℝ) ^ 2 := by
  let f := cylinderFunction (n + 1) (density (n + 1))
  let g := cylinderFunction n (density n)
  have hf : Integrable (fun x => f x ^ 2) unitHaar :=
    integrable_cylinderFunction unitHaar (n + 1) (fun r => density (n + 1) r ^ 2)
  have hg : Integrable (fun x => g x ^ 2) unitHaar :=
    integrable_cylinderFunction unitHaar n (fun r => density n r ^ 2)
  have hupper : (∫ x, densityIncrement n x ^ 2 ∂unitHaar) ≤
      ∫ x, 2 * (f x ^ 2 + g x ^ 2) ∂unitHaar := by
    apply integral_mono (integrable_densityIncrement_sq n) ((hf.add hg).const_mul 2)
    intro x
    change (f x - g x) ^ 2 ≤ 2 * (f x ^ 2 + g x ^ 2)
    nlinarith [sq_nonneg (f x + g x)]
  rw [integral_const_mul, integral_add hf hg] at hupper
  have h1 := integral_density_sq_le_eight_sq (n + 1) (by omega)
  have h0 := integral_density_sq_le_eight_sq n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  push_cast at h1
  change (∫ x, f x ^ 2 ∂unitHaar) ≤ _ at h1
  change (∫ x, g x ^ 2 ∂unitHaar) ≤ _ at h0
  nlinarith

/-- Every inverse-power rate is available, with its own finite constant. -/
theorem densityIncrement_L1_all_orders (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ x, |densityIncrement n x| ∂unitHaar) ≤ C / (n : ℝ) ^ A := by
  obtain ⟨C, hC, hmix⟩ := paper_thm_mixing A hA
  refine ⟨C, hC, ?_⟩
  intro n hn
  unfold densityIncrement
  rw [integral_abs_density_difference_unitHaar hn (Nat.le_succ n)]
  have h := mul_le_mul_of_nonneg_left
    (hmix (n + 1) n hn (Nat.le_succ n)) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  convert h using 1 <;> ring

end SyracuseReport
