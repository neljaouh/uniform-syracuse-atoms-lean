import PaperStatements
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Transfer from a good residue class to all signed targets, including
the logarithmic exponent limit. The good-root hypothesis is explicit here;
its separate quantitative word proof is required by the paper gate. -/

namespace SyracuseReport
open Filter
open scoped Topology

theorem Reaches.trans {m R a : ℤ} (hm : Reaches m R) (hR : Reaches R a) :
    Reaches m a := by
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := hR
  exact ⟨j + i, by rw [Function.iterate_add_apply, hi, hj]⟩

theorem oddRootPredecessorCount_le {R a : ℤ} (hR : Reaches R a) (x : ℝ) :
    oddRootPredecessorCount R x ≤ predecessorCount a x := by
  classical
  apply Finset.card_le_card
  intro m hm
  simp only [oddRootPredecessorCount, Finset.mem_filter] at hm
  simp only [predecessorCount, Finset.mem_filter]
  exact ⟨hm.1, hm.2.2.1.trans hR⟩

theorem predecessorCount_upper (a : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    (predecessorCount a x : ℝ) ≤ 3 * x := by
  classical
  have hf : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr (by linarith)
  have hab : ⌈-x⌉ ≤ ⌊x⌋ + 1 := by rw [Int.ceil_neg]; omega
  have hc := Int.card_Icc_of_le ⌈-x⌉ ⌊x⌋ hab
  have hcR : (((Finset.Icc ⌈-x⌉ ⌊x⌋).card : ℕ) : ℝ) =
      (⌊x⌋ : ℝ) + 1 - (⌈-x⌉ : ℝ) := by exact_mod_cast hc
  have hfilter : predecessorCount a x ≤ (Finset.Icc ⌈-x⌉ ⌊x⌋).card :=
    Finset.card_filter_le _ _
  have hfilterR : (predecessorCount a x : ℝ) ≤
      (((Finset.Icc ⌈-x⌉ ⌊x⌋).card : ℕ) : ℝ) := by exact_mod_cast hfilter
  rw [hcR, Int.ceil_neg, Int.cast_neg] at hfilterR
  have := Int.floor_le x
  linarith

/-- A unit-coefficient lower bound at every exponent below one,
together with the elementary interval upper bound, gives the full limit. -/
theorem predecessor_log_exponent_of_lower (a : ℤ)
    (hlower : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧
      ∀ x : ℝ, x0 ≤ x → x ^ (1 - eps) ≤ (predecessorCount a x : ℝ)) :
    Tendsto (fun x : ℝ => Real.log (predecessorCount a x) / Real.log x)
      atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let eps : ℝ := (1 - b) / 2
    have heps : 0 < eps := by dsimp [eps]; linarith
    obtain ⟨x0, hx0, hbound⟩ := hlower eps heps
    filter_upwards [eventually_ge_atTop x0] with x hx
    have hx1 : 1 < x := by linarith
    have hxpos : 0 < x := by linarith
    have hpow : 0 < x ^ (1 - eps) := Real.rpow_pos_of_pos hxpos _
    have hcountpos : 0 < (predecessorCount a x : ℝ) := hpow.trans_le (hbound x hx)
    have hlog := Real.log_le_log hpow (hbound x hx)
    rw [Real.log_rpow hxpos] at hlog
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hquot : 1 - eps ≤ Real.log (predecessorCount a x) / Real.log x :=
      (le_div_iff₀ hlogpos).mpr hlog
    have hb' : b < 1 - eps := by dsimp [eps]; linarith
    exact hb'.trans_le hquot
  · intro b hb
    have hlim : Tendsto (fun x : ℝ => (1 : ℝ) + Real.log 3 / Real.log x)
        atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
    have hevent : ∀ᶠ x : ℝ in atTop, 1 + Real.log 3 / Real.log x < b :=
      hlim.eventually (eventually_lt_nhds (by simpa using hb))
    obtain ⟨x0, hx0, hbound⟩ := hlower 1 (by norm_num)
    filter_upwards [hevent, eventually_ge_atTop x0] with x hupper hx
    have hx1 : 1 < x := by linarith
    have hxpos : 0 < x := by linarith
    have hcountpos : 0 < (predecessorCount a x : ℝ) := by
      have hp := hbound x hx
      have hpR : (1 : ℝ) ≤ (predecessorCount a x : ℝ) := by
        simpa only [sub_self, Real.rpow_zero] using hp
      exact zero_lt_one.trans_le hpR
    have hlog := Real.log_le_log hcountpos (predecessorCount_upper a hx1.le)
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hquot := div_le_div_of_nonneg_right hlog hlogpos.le
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hxpos.ne', add_div,
      div_self hlogpos.ne'] at hquot
    exact hquot.trans_lt (by linarith)

theorem counting_of_good_roots (hgood : PaperStatements.lem_good_roots) :
    PaperStatements.thm_counting := by
  intro hatom a ha
  have hlower : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧
      ∀ x : ℝ, x0 ≤ x → x ^ (1 - eps) ≤ (predecessorCount a x : ℝ) := by
    intro eps heps
    obtain ⟨q, y, hq, hy, hroots⟩ := hgood hatom (1 - eps) (by linarith)
    obtain ⟨R, hRodd, hRy, hRa, _, _⟩ := signed_seed_in_residue a ha q hq y 0
    obtain ⟨x0, hx0, hcounts⟩ := hroots R hRodd hRy
    refine ⟨x0, hx0, ?_⟩
    intro x hx
    exact (hcounts x hx).trans (by exact_mod_cast oddRootPredecessorCount_le hRa x)
  exact ⟨hlower, predecessor_log_exponent_of_lower a hlower⟩

theorem uniform_counting_of_good_roots (hgood : PaperStatements.lem_good_roots) :
    PaperStatements.cor_uniform :=
  paper_cor_uniform_of_counting (counting_of_good_roots hgood)

end SyracuseReport
