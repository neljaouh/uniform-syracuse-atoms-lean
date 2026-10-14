import SquareRootProfile

/-! Every sufficiently large real cutoff admits an integer word length with
square-root logarithmic loss and the actual logarithmic shortcut clock. -/
namespace SyracuseReport
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem sqrtLog_mul_small_eventually (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop,A*sqrtLogProfile y ≤ y/(2*c) := by
  have hlim := sqrtLogProfile_div_rpow_tendsto (r := 1) (by norm_num)
  simp only [Real.rpow_one] at hlim
  have he := hlim.eventually (eventually_lt_nhds (show 0 < 1/(2*c*A) by positivity))
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with y hy hp
  have hr := (div_le_iff₀ hp).1 hy.le
  have hm := mul_le_mul_of_nonneg_left hr hA.le
  have heq : A*((1/(2*c*A))*y)=y/(2*c) := by field_simp [hc.ne',hA.ne'] <;> ring
  simpa only [heq] using hm

theorem affine_le_exp_half_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, y / c + 1 ≤ Real.exp (y ^ (1 / 2 : ℝ)) := by
  have hx := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hpoly := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 : ℝ) 1 (by norm_num)).comp hx
  have hconst := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  have hsum := (hpoly.const_mul (1 / c)).add hconst
  have hsum0 := hsum
  simp only [mul_zero, zero_add] at hsum0
  have hev := hsum0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with y hy hpos
  have heq : (y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = y := by
    rw [← Real.rpow_mul hpos.le]
    norm_num
  dsimp only [Function.comp_apply] at hy
  rw [heq] at hy
  simp only [neg_mul, one_mul] at hy
  have hb : (y / c + 1) * Real.exp (-(y ^ (1 / 2 : ℝ))) ≤ 1 := by
    have he : (y / c + 1) * Real.exp (-(y ^ (1 / 2 : ℝ))) =
        (1 / c) * (y * Real.exp (-(y ^ (1 / 2 : ℝ)))) +
          Real.exp (-(y ^ (1 / 2 : ℝ))) := by ring
    rw [he]
    exact hy.le
  have hmul := mul_le_mul_of_nonneg_right hb (Real.exp_pos (y ^ (1 / 2 : ℝ))).le
  have hexp : Real.exp (-(y ^ (1 / 2 : ℝ))) * Real.exp (y ^ (1 / 2 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  simpa only [mul_assoc, hexp, mul_one, one_mul] using hmul

theorem affine_le_exp_sqrtLog_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop,y/c+1 ≤ Real.exp (sqrtLogProfile y) := by
  filter_upwards [affine_le_exp_half_eventually c hc,eventually_ge_atTop (Real.exp 1)] with y hy hye
  apply hy.trans
  apply Real.exp_le_exp.mpr
  simpa only [Real.sqrt_eq_rpow] using sqrtLogProfile_ge_sqrt hye

theorem sqrtLog_cutoff_witness
    (c k K kappa M Q : ℝ) (J H : ℕ)
    (hc : 0 < c) (hclower : (1/8 : ℝ) ≤ c) (hk : 0 < k) (hK : 0 < K)
    (hkappa : 0 < kappa) (hM : 0 < M) (hQ : 0 < Q) (hH : 2 ≤ H) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∃ h : ℕ, H ≤ h ∧
        Q * Real.exp (c * h + k * sqrtLogProfile h) ≤ x ∧
        ((kappa * (3 / 2 : ℝ) / M) * Real.exp (-c)) * x *
          Real.exp (-(2 * k * (8 : ℝ) + 3) *
            sqrtLogProfile (Real.log x)) ≤
          (kappa / (M * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
            Real.exp (c * h - k * sqrtLogProfile h) ∧
        2 * (h : ℝ) + K * sqrtLogProfile h + J ≤
          (2 / c) * Real.log x +
            (K * (8 : ℝ) + J) * sqrtLogProfile (Real.log x) := by
  let d : ℝ := 8
  let A : ℝ := (k * d + 2) / c
  have hd : 0 < d := by norm_num [d]
  have hA : 0 < A := by dsimp [A]; positivity
  have hAeq : c * A = k * d + 2 := by dsimp [A]; field_simp
  have hroot : ∀ᶠ y : ℝ in atTop, Real.log Q ≤ 2 * sqrtLogProfile y :=
    (sqrtLogProfile_tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)).eventually (eventually_ge_atTop (Real.log Q))
  have hev := (sqrtLog_mul_small_eventually A c hA hc).and
    ((affine_le_exp_sqrtLog_eventually c hc).and
      (hroot.and ((eventually_ge_atTop (2 : ℝ)).and
        ((eventually_ge_atTop (Real.exp 1)).and
          (eventually_ge_atTop (2 * c * ((H : ℝ) + 1)))))))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  let x0 : ℝ := max 2 (Real.exp Y)
  refine ⟨x0, le_max_left _ _, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hYx : Y ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).mpr ((le_max_right _ _).trans hx)
  obtain ⟨hsmall, hden, hrootx, hy2, hyexp, hyH⟩ := hY (Real.log x) hYx
  let y : ℝ := Real.log x
  have hy : 0 < y := by dsimp [y]; linarith
  have hPhi := sqrtLogProfile_nonneg y
  let z : ℝ := y / c - A * sqrtLogProfile y
  have hylow : (H : ℝ) + 1 ≤ y / (2 * c) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * c)).mpr
    dsimp [y]
    nlinarith only [hyH]
  have hzH : (H : ℝ) + 1 ≤ z := by
    change A * sqrtLogProfile y ≤ y / (2 * c) at hsmall
    have hhalf : y / c = 2 * (y / (2 * c)) := by
      field_simp [hc.ne']
      <;> ring
    dsimp [z]
    linarith
  have hz : 0 ≤ z := by
    have hH0 : (0 : ℝ) ≤ H := by positivity
    linarith
  let h : ℕ := Nat.floor z
  have hhH : H ≤ h := Nat.le_floor (by linarith : (H : ℝ) ≤ z)
  have hfloor : (h : ℝ) ≤ z := Nat.floor_le hz
  have hround : z < (h : ℝ) + 1 := Nat.lt_floor_add_one z
  have hle : (h : ℝ) ≤ y / c := by
    have hp : 0 ≤ A * sqrtLogProfile y := by positivity
    dsimp [z] at hfloor
    linarith
  have hhs : (h : ℝ) ≤ 8*y := by
    apply hle.trans
    apply (div_le_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_right hclower hy.le]
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hpow : sqrtLogProfile h ≤ d*sqrtLogProfile y :=
    (sqrtLogProfile_mono hh1 hhs).trans (sqrtLogProfile_scale_eight hy2)
  have hcz : c * z = y - (k * d + 2) * sqrtLogProfile y := by
    dsimp [z, A]
    field_simp [hc.ne']
    <;> ring
  have hchupper : c * (h : ℝ) + k * sqrtLogProfile h ≤ y - 2 * sqrtLogProfile y := by
    have hf := mul_le_mul_of_nonneg_left hfloor hc.le
    have hp := mul_le_mul_of_nonneg_left hpow hk.le
    rw [hcz] at hf
    nlinarith only [hf, hp]
  have hchlower : y - (2 * k * d + 3) * sqrtLogProfile y - c ≤
      c * (h : ℝ) - k * sqrtLogProfile h - sqrtLogProfile y := by
    have hf := mul_lt_mul_of_pos_left hround hc
    have hp := mul_le_mul_of_nonneg_left hpow hk.le
    rw [hcz] at hf
    nlinarith only [hf, hp]
  have hdenh : (h : ℝ) + 1 ≤ Real.exp (sqrtLogProfile y) := by
    calc
      _ ≤ y / c + 1 := by linarith only [hle]
      _ ≤ _ := hden
  have hdenpos : 0 < (h : ℝ) + 1 := by positivity
  have hrecip : Real.exp (-(sqrtLogProfile y)) ≤ 1 / ((h : ℝ) + 1) := by
    apply (le_div_iff₀ hdenpos).mpr
    have hm := mul_le_mul_of_nonneg_left hdenh (Real.exp_pos (-(sqrtLogProfile y))).le
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using hm
  refine ⟨h, hhH, ?_, ?_, ?_⟩
  · have he : Real.log Q + (c * (h : ℝ) + k * sqrtLogProfile h) ≤ y := by
      linarith only [hchupper, hrootx]
    have hm := Real.exp_le_exp.mpr he
    rw [Real.exp_add, Real.exp_log hQ, Real.exp_log hxpos] at hm
    exact hm
  · let A0 : ℝ := kappa * (3 / 2 : ℝ) / M
    have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hchlower) hA0
    have hr := mul_le_mul_of_nonneg_left hrecip hA0
    have hp := mul_le_mul_of_nonneg_right hr
      (Real.exp_pos (c * (h : ℝ) - k * sqrtLogProfile h)).le
    have hcoef : (kappa / (M * ((h : ℝ) + 1))) * (3 / 2 : ℝ) =
        A0 / ((h : ℝ) + 1) := by
      dsimp [A0]
      field_simp [hM.ne', hdenpos.ne']
    change (A0 * Real.exp (-c)) * x * Real.exp (-(2 * k * d + 3) * sqrtLogProfile y) ≤ _
    rw [hcoef]
    calc
      _ = A0 * Real.exp (y - (2 * k * d + 3) * sqrtLogProfile y - c) := by
        have hxexp : Real.exp y = x := Real.exp_log hxpos
        rw [← hxexp, show y - (2 * k * d + 3) * sqrtLogProfile y - c =
          y + (-(2 * k * d + 3) * sqrtLogProfile y) + (-c) by ring,
          Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := he
      _ = (A0 * Real.exp (-(sqrtLogProfile y))) *
          Real.exp (c * (h : ℝ) - k * sqrtLogProfile h) := by
        rw [show c * (h : ℝ) - k * sqrtLogProfile h - sqrtLogProfile y =
          -(sqrtLogProfile y) + (c * (h : ℝ) - k * sqrtLogProfile h) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using hp
  · have htime := mul_le_mul_of_nonneg_left hpow hK.le
    have hpowone : 1 ≤ sqrtLogProfile y := sqrtLogProfile_ge_one hy2
    have hJ := mul_le_mul_of_nonneg_left hpowone (show (0 : ℝ) ≤ J by positivity)
    have ht2 : 2 * (h : ℝ) ≤ (2 / c) * y := by
      calc
        _ ≤ 2 * (y / c) := mul_le_mul_of_nonneg_left hle (by norm_num)
        _ = _ := by ring
    change 2 * (h : ℝ) + K * sqrtLogProfile h + J ≤
      (2 / c) * y + (K * d + J) * sqrtLogProfile y
    nlinarith only [ht2, htime, hJ]

end SyracuseReport
