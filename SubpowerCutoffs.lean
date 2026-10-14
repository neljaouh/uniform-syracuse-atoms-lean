import CountingCompletion

/-! Analytic passage from every large integer word length to every large
real cutoff, preserving a subpower counting loss and a logarithmic clock. -/
namespace SyracuseReport
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem subpower_mul_small_eventually (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, A * y ^ (3 / 5 : ℝ) ≤ y / (2 * c) := by
  have hlim := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)
  have hev := hlim.eventually (eventually_lt_nhds (show 0 < 1 / (2 * c * A) by positivity))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with y hy hpos
  have heq : y * y ^ (-(2 / 5 : ℝ)) = y ^ (3 / 5 : ℝ) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (-(2 / 5 : ℝ)) := by rw [Real.rpow_one]
      _ = y ^ ((1 : ℝ) + -(2 / 5 : ℝ)) := (Real.rpow_add hpos _ _).symm
      _ = _ := by norm_num
  have hprod := mul_le_mul_of_nonneg_left hy.le (show 0 ≤ A * y by positivity)
  have hlo : (A * y) * y ^ (-(2 / 5 : ℝ)) = A * y ^ (3 / 5 : ℝ) := by
    rw [mul_assoc, heq]
  rw [hlo] at hprod
  have hright : (A * y) * (1 / (2 * c * A)) = y / (2 * c) := by
    field_simp [hc.ne', hA.ne']
  rwa [hright] at hprod

theorem affine_le_exp_subpower_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, y / c + 1 ≤ Real.exp (y ^ (3 / 5 : ℝ)) := by
  have hx := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)
  have hpoly := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (5 / 3 : ℝ) 1 (by norm_num)).comp hx
  have hconst := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  have hsum := (hpoly.const_mul (1 / c)).add hconst
  have hsum0 := hsum
  simp only [mul_zero, zero_add] at hsum0
  have hev := hsum0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with y hy hpos
  have heq : (y ^ (3 / 5 : ℝ)) ^ (5 / 3 : ℝ) = y := by
    rw [← Real.rpow_mul hpos.le]
    norm_num
  dsimp only [Function.comp_apply] at hy
  rw [heq] at hy
  simp only [neg_mul, one_mul] at hy
  have hb : (y / c + 1) * Real.exp (-(y ^ (3 / 5 : ℝ))) ≤ 1 := by
    have he : (y / c + 1) * Real.exp (-(y ^ (3 / 5 : ℝ))) =
        (1 / c) * (y * Real.exp (-(y ^ (3 / 5 : ℝ)))) +
          Real.exp (-(y ^ (3 / 5 : ℝ))) := by ring
    rw [he]
    exact hy.le
  have hmul := mul_le_mul_of_nonneg_right hb (Real.exp_pos (y ^ (3 / 5 : ℝ))).le
  have hexp : Real.exp (-(y ^ (3 / 5 : ℝ))) * Real.exp (y ^ (3 / 5 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  simpa only [mul_assoc, hexp, mul_one, one_mul] using hmul

theorem subpower_cutoff_witness
    (c k K kappa M Q : ℝ) (J H : ℕ)
    (hc : 0 < c) (hk : 0 < k) (hK : 0 < K)
    (hkappa : 0 < kappa) (hM : 0 < M) (hQ : 0 < Q) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∃ h : ℕ, H ≤ h ∧
        Q * Real.exp (c * h + k * (h : ℝ) ^ (3 / 5 : ℝ)) ≤ x ∧
        ((kappa * (3 / 2 : ℝ) / M) * Real.exp (-c)) * x *
          Real.exp (-(2 * k * c ^ (-(3 / 5 : ℝ)) + 3) *
            (Real.log x) ^ (3 / 5 : ℝ)) ≤
          (kappa / (M * ((h : ℝ) + 1))) * (3 / 2 : ℝ) *
            Real.exp (c * h - k * (h : ℝ) ^ (3 / 5 : ℝ)) ∧
        2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ) + J ≤
          (2 / c) * Real.log x +
            (K * c ^ (-(3 / 5 : ℝ)) + J) * (Real.log x) ^ (3 / 5 : ℝ) := by
  let d : ℝ := c ^ (-(3 / 5 : ℝ))
  let A : ℝ := (k * d + 2) / c
  have hd : 0 < d := Real.rpow_pos_of_pos hc _
  have hA : 0 < A := by dsimp [A]; positivity
  have hAeq : c * A = k * d + 2 := by dsimp [A]; field_simp
  have hroot : ∀ᶠ y : ℝ in atTop, Real.log Q ≤ 2 * y ^ (3 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)).eventually (eventually_ge_atTop (Real.log Q))
  have hev := (subpower_mul_small_eventually A c hA hc).and
    ((affine_le_exp_subpower_eventually c hc).and
      (hroot.and ((eventually_ge_atTop (1 : ℝ)).and
        (eventually_ge_atTop (2 * c * ((H : ℝ) + 1))))))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  let x0 : ℝ := max 2 (Real.exp Y)
  refine ⟨x0, le_max_left _ _, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hYx : Y ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).mpr ((le_max_right _ _).trans hx)
  obtain ⟨hsmall, hden, hrootx, hy1, hyH⟩ := hY (Real.log x) hYx
  let y : ℝ := Real.log x
  have hy : 0 < y := by dsimp [y]; linarith
  let z : ℝ := y / c - A * y ^ (3 / 5 : ℝ)
  have hylow : (H : ℝ) + 1 ≤ y / (2 * c) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * c)).mpr
    dsimp [y]
    nlinarith only [hyH]
  have hzH : (H : ℝ) + 1 ≤ z := by
    change A * y ^ (3 / 5 : ℝ) ≤ y / (2 * c) at hsmall
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
    have hp : 0 ≤ A * y ^ (3 / 5 : ℝ) := by positivity
    dsimp [z] at hfloor
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ h) hle
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hdiv : (y / c) ^ (3 / 5 : ℝ) = d * y ^ (3 / 5 : ℝ) := by
    rw [Real.div_rpow hy.le hc.le]
    dsimp [d]
    rw [Real.rpow_neg hc.le]
    ring
  rw [hdiv] at hpow
  have hcz : c * z = y - (k * d + 2) * y ^ (3 / 5 : ℝ) := by
    dsimp [z, A]
    field_simp [hc.ne']
    <;> ring
  have hchupper : c * (h : ℝ) + k * (h : ℝ) ^ (3 / 5 : ℝ) ≤ y - 2 * y ^ (3 / 5 : ℝ) := by
    have hf := mul_le_mul_of_nonneg_left hfloor hc.le
    have hp := mul_le_mul_of_nonneg_left hpow hk.le
    rw [hcz] at hf
    nlinarith only [hf, hp]
  have hchlower : y - (2 * k * d + 3) * y ^ (3 / 5 : ℝ) - c ≤
      c * (h : ℝ) - k * (h : ℝ) ^ (3 / 5 : ℝ) - y ^ (3 / 5 : ℝ) := by
    have hf := mul_lt_mul_of_pos_left hround hc
    have hp := mul_le_mul_of_nonneg_left hpow hk.le
    rw [hcz] at hf
    nlinarith only [hf, hp]
  have hdenh : (h : ℝ) + 1 ≤ Real.exp (y ^ (3 / 5 : ℝ)) := by
    calc
      _ ≤ y / c + 1 := by linarith only [hle]
      _ ≤ _ := hden
  have hdenpos : 0 < (h : ℝ) + 1 := by positivity
  have hrecip : Real.exp (-(y ^ (3 / 5 : ℝ))) ≤ 1 / ((h : ℝ) + 1) := by
    apply (le_div_iff₀ hdenpos).mpr
    have hm := mul_le_mul_of_nonneg_left hdenh (Real.exp_pos (-(y ^ (3 / 5 : ℝ)))).le
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using hm
  refine ⟨h, hhH, ?_, ?_, ?_⟩
  · have he : Real.log Q + (c * (h : ℝ) + k * (h : ℝ) ^ (3 / 5 : ℝ)) ≤ y := by
      linarith only [hchupper, hrootx]
    have hm := Real.exp_le_exp.mpr he
    rw [Real.exp_add, Real.exp_log hQ, Real.exp_log hxpos] at hm
    exact hm
  · let A0 : ℝ := kappa * (3 / 2 : ℝ) / M
    have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hchlower) hA0
    have hr := mul_le_mul_of_nonneg_left hrecip hA0
    have hp := mul_le_mul_of_nonneg_right hr
      (Real.exp_pos (c * (h : ℝ) - k * (h : ℝ) ^ (3 / 5 : ℝ))).le
    have hcoef : (kappa / (M * ((h : ℝ) + 1))) * (3 / 2 : ℝ) =
        A0 / ((h : ℝ) + 1) := by
      dsimp [A0]
      field_simp [hM.ne', hdenpos.ne']
    change (A0 * Real.exp (-c)) * x * Real.exp (-(2 * k * d + 3) * y ^ (3 / 5 : ℝ)) ≤ _
    rw [hcoef]
    calc
      _ = A0 * Real.exp (y - (2 * k * d + 3) * y ^ (3 / 5 : ℝ) - c) := by
        have hxexp : Real.exp y = x := Real.exp_log hxpos
        rw [← hxexp, show y - (2 * k * d + 3) * y ^ (3 / 5 : ℝ) - c =
          y + (-(2 * k * d + 3) * y ^ (3 / 5 : ℝ)) + (-c) by ring,
          Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := he
      _ = (A0 * Real.exp (-(y ^ (3 / 5 : ℝ)))) *
          Real.exp (c * (h : ℝ) - k * (h : ℝ) ^ (3 / 5 : ℝ)) := by
        rw [show c * (h : ℝ) - k * (h : ℝ) ^ (3 / 5 : ℝ) - y ^ (3 / 5 : ℝ) =
          -(y ^ (3 / 5 : ℝ)) + (c * (h : ℝ) - k * (h : ℝ) ^ (3 / 5 : ℝ)) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using hp
  · have htime := mul_le_mul_of_nonneg_left hpow hK.le
    have hpowone : 1 ≤ y ^ (3 / 5 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
    have hJ := mul_le_mul_of_nonneg_left hpowone (show (0 : ℝ) ≤ J by positivity)
    have ht2 : 2 * (h : ℝ) ≤ (2 / c) * y := by
      calc
        _ ≤ 2 * (y / c) := mul_le_mul_of_nonneg_left hle (by norm_num)
        _ = _ := by ring
    change 2 * (h : ℝ) + K * (h : ℝ) ^ (3 / 5 : ℝ) + J ≤
      (2 / c) * y + (K * d + J) * y ^ (3 / 5 : ℝ)
    nlinarith only [ht2, htime, hJ]

end SyracuseReport
