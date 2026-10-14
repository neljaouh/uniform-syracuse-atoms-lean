import Minimum
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Instances.Real.Lemmas

namespace SyracuseReport
open scoped BigOperators Topology
open Filter

theorem card_units_at_depth (n : ℕ) :
    Fintype.card (ZMod (3 ^ (n + 1)))ˣ = 2 * 3 ^ n := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_three]
  norm_num
  ring

theorem sum_unit_masses_le_one (n : ℕ) :
    ∑ u : (ZMod (3 ^ (n + 1)))ˣ,
      (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal ≤ 1 := by
  have hinj : Function.Injective
      (fun u : (ZMod (3 ^ (n + 1)))ˣ => (u : ZMod (3 ^ (n + 1)))) :=
    Units.val_injective
  have hmap : ∑ u : (ZMod (3 ^ (n + 1)))ˣ,
      (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal =
      ∑ r ∈ Finset.univ.map ⟨_, hinj⟩, (syracuseLaw (n + 1) r).toReal := by
    rw [Finset.sum_map]
    rfl
  rw [hmap, ← syracuseLaw_real_sum (n + 1)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => ENNReal.toReal_nonneg)

theorem leastAtom_upper (n : ℕ) :
    leastAtom n ≤ (3 / 2 : ℝ) / (3 : ℝ) ^ (n + 1) := by
  by_contra hnot
  have hall : ∀ u : (ZMod (3 ^ (n + 1)))ˣ,
      (3 / 2 : ℝ) / (3 : ℝ) ^ (n + 1) <
        (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal := by
    intro u
    exact lt_of_not_ge (fun h => hnot (leastAtom_le n u |>.trans h))
  have hsum : ∑ _u : (ZMod (3 ^ (n + 1)))ˣ,
      (3 / 2 : ℝ) / (3 : ℝ) ^ (n + 1) <
      ∑ u : (ZMod (3 ^ (n + 1)))ˣ,
        (syracuseLaw (n + 1) (u : ZMod (3 ^ (n + 1)))).toReal := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro u _
    exact hall u
  rw [Finset.sum_const, Finset.card_univ, card_units_at_depth,
    nsmul_eq_mul] at hsum
  have heq : ((2 * 3 ^ n : ℕ) : ℝ) *
      ((3 / 2 : ℝ) / (3 : ℝ) ^ (n + 1)) = 1 := by
    push_cast
    rw [pow_succ]
    field_simp
  linarith [sum_unit_masses_le_one n]

theorem normalizedMinimum_upper (n : ℕ) : normalizedMinimum n ≤ 3 / 2 := by
  have h := mul_le_mul_of_nonneg_left (leastAtom_upper n)
    (by positivity : (0 : ℝ) ≤ 3 ^ (n + 1))
  unfold normalizedMinimum
  have hp : (3 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  field_simp at h
  linarith

theorem normalizedMinimum_lower_of_floor {c : ℝ} (hF : FloorAt c) (n : ℕ) :
    c ≤ normalizedMinimum n := by
  have hmin : c / (3 : ℝ) ^ (n + 1) ≤ leastAtom n := by
    apply le_leastAtom
    intro u
    exact hF (n + 1) (by omega) u u.isUnit
  have h := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ 3 ^ (n + 1))
  unfold normalizedMinimum
  have hp : (3 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  field_simp at h
  exact h

theorem exists_normalizedMinimum_limit {c : ℝ} (hc : 0 < c) (hF : FloorAt c) :
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ 3 / 2 ∧
      Tendsto normalizedMinimum atTop (𝓝 ell) := by
  let ell := ⨅ n, normalizedMinimum n
  have hbdd : BddBelow (Set.range normalizedMinimum) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact mul_nonneg (by positivity) (leastAtom_nonneg n)
  have hlim : Tendsto normalizedMinimum atTop (𝓝 ell) :=
    tendsto_atTop_ciInf normalizedMinimum_antitone hbdd
  have hlower : c ≤ ell := by
    dsimp [ell]
    exact le_ciInf fun n => normalizedMinimum_lower_of_floor hF n
  have hupper : ell ≤ 3 / 2 := by
    dsimp [ell]
    exact (ciInf_le hbdd 0).trans (normalizedMinimum_upper 0)
  exact ⟨ell, hc.trans_le hlower, hupper, hlim⟩

theorem leastAtom_ratio_identity (ell : ℝ) (hell : ell ≠ 0) (n : ℕ) :
    leastAtom n / (ell / (3 : ℝ) ^ (n + 1)) = normalizedMinimum n / ell := by
  unfold normalizedMinimum
  have hp : (3 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  field_simp

theorem tendsto_leastAtom_ratio {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto normalizedMinimum atTop (𝓝 ell)) :
    Tendsto (fun n => leastAtom n / (ell / (3 : ℝ) ^ (n + 1)))
      atTop (𝓝 1) := by
  have hdiv := hlim.div tendsto_const_nhds hell.ne'
  have hone : ell / ell = (1 : ℝ) := div_self hell.ne'
  rw [hone] at hdiv
  exact hdiv.congr' (Filter.Eventually.of_forall fun n =>
    (leastAtom_ratio_identity ell hell.ne' n).symm)

theorem minimumExponent_identity {c : ℝ} (hc : 0 < c) (hF : FloorAt c) (n : ℕ) :
    minimumExponent n =
      1 - Real.log (normalizedMinimum n) /
        (((n + 1 : ℕ) : ℝ) * Real.log 3) := by
  have hmpos : 0 < normalizedMinimum n := hc.trans_le (normalizedMinimum_lower_of_floor hF n)
  have hp : (3 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  have hleast : leastAtom n = normalizedMinimum n / (3 : ℝ) ^ (n + 1) := by
    unfold normalizedMinimum
    field_simp
  unfold minimumExponent
  rw [hleast, Real.log_div hmpos.ne' hp, Real.log_pow]
  have hlog3 : Real.log (3 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp
  ring

theorem tendsto_minimumExponent_one {c ell : ℝ} (hc : 0 < c) (hF : FloorAt c)
    (hell : 0 < ell) (hlim : Tendsto normalizedMinimum atTop (𝓝 ell)) :
    Tendsto minimumExponent atTop (𝓝 1) := by
  have hlog : Tendsto (fun n => Real.log (normalizedMinimum n)) atTop
      (𝓝 (Real.log ell)) := (Real.continuousAt_log hell.ne').tendsto.comp hlim
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hmul := hlog.mul hinv
  have hzero : Tendsto
      (fun n => Real.log (normalizedMinimum n) /
        (((n + 1 : ℕ) : ℝ) * Real.log 3)) atTop (𝓝 0) := by
    have hlog3 : Real.log (3 : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    have hdiv := hmul.div tendsto_const_nhds hlog3
    convert hdiv using 1
    · funext n
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      simp only [Pi.div_apply, one_div]
      change Real.log (normalizedMinimum n) /
          (((n + 1 : ℕ) : ℝ) * Real.log 3) =
        (Real.log (normalizedMinimum n) / ((n + 1 : ℕ) : ℝ)) / Real.log 3
      field_simp [hn, hlog3]
    · simp
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) -
      Real.log (normalizedMinimum n) /
        (((n + 1 : ℕ) : ℝ) * Real.log 3)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  exact hone.congr' (Filter.Eventually.of_forall fun n =>
    (minimumExponent_identity hc hF n).symm)

theorem floor_of_positive_normalizedMinimum_limit {ell : ℝ} (_hell : 0 < ell)
    (hlim : Tendsto normalizedMinimum atTop (𝓝 ell)) : FloorAt ell := by
  intro d hd r hr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hlimit_le : ell ≤ normalizedMinimum n := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop n] with j hj
    exact normalizedMinimum_antitone hj
  have hatom := leastAtom_le_of_isUnit n r hr
  have hmul : ell ≤ (3 : ℝ) ^ (n + 1) * (syracuseLaw (n + 1) r).toReal :=
    hlimit_le.trans <| by
      unfold normalizedMinimum
      exact mul_le_mul_of_nonneg_left hatom (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ (n + 1))).2
  simpa only [Nat.succ_eq_add_one, mul_comm] using hmul

/-- Exact formal statement of Proposition `minimum` in the manuscript. -/
def MinimumAsymptoticsStatement : Prop :=
  Antitone normalizedMinimum ∧
  (AtomFloorStatement ↔ ∃ ell : ℝ, 0 < ell ∧
    Tendsto normalizedMinimum atTop (𝓝 ell)) ∧
  ∀ c : ℝ, 0 < c → FloorAt c →
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ 3 / 2 ∧
      Tendsto normalizedMinimum atTop (𝓝 ell) ∧
      Tendsto (fun n => leastAtom n / (ell / (3 : ℝ) ^ (n + 1))) atTop (𝓝 1) ∧
      Tendsto minimumExponent atTop (𝓝 1)

theorem minimum_asymptotics : MinimumAsymptoticsStatement := by
  refine ⟨normalizedMinimum_antitone, ?_, ?_⟩
  · constructor
    · rintro ⟨c, hc, hF⟩
      obtain ⟨ell, hell, _, hlim⟩ := exists_normalizedMinimum_limit hc hF
      exact ⟨ell, hell, hlim⟩
    · rintro ⟨ell, hell, hlim⟩
      exact ⟨ell, hell, floor_of_positive_normalizedMinimum_limit hell hlim⟩
  · intro c hc hF
    obtain ⟨ell, hell, hupper, hlim⟩ := exists_normalizedMinimum_limit hc hF
    exact ⟨ell, hell, hupper, hlim, tendsto_leastAtom_ratio hell hlim,
      tendsto_minimumExponent_one hc hF hell hlim⟩

end SyracuseReport
