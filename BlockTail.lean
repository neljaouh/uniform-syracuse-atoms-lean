import BlockMoment

/-! Chernoff estimates for the centered geometric block total. -/

namespace SyracuseReport
open Erdos1135.Tao

theorem centeredList_expTail_le (N : ℕ) {t lambda : ℝ}
    (ht : |t| ≤ 1 / 4) :
    ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < t * taoGeom2CenteredListWeight as}).toReal ≤
      Real.exp (-lambda + 3 * t ^ 2 * N) := by
  let F : List ℕ+ → ENNReal := fun as =>
    ENNReal.ofReal (Real.exp (t * taoGeom2CenteredListWeight as))
  let cutoff := ENNReal.ofReal (Real.exp lambda)
  have hadm : Real.exp t < 2 := by
    have hh := exp_sub_one_abs_le_four_thirds ht
    have ha := le_abs_self (Real.exp t - 1)
    linarith
  have hevent : {as | cutoff < F as} =
      {as | lambda < t * taoGeom2CenteredListWeight as} := by
    ext as
    simp only [Set.mem_setOf_eq, F, cutoff]
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp]
  have hmarkov := tao_pmfToOuterMeasure_gt_mul_le_expectation
    (geom2PNatListPMF N) F cutoff
  rw [hevent] at hmarkov
  have hexpect : taoPMFENNExpectation (geom2PNatListPMF N) F =
      ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N := by
    simpa [F] using geom2PNatListPMF_centeredExpMoment_ennreal N hadm
  rw [hexpect] at hmarkov
  have hreal := ENNReal.toReal_mono
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmarkov
  have hmul : ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < t * taoGeom2CenteredListWeight as}).toReal *
      Real.exp lambda ≤ taoGeom2CenteredExpMoment t ^ N := by
    simpa [cutoff, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (taoGeom2CenteredExpMoment_nonneg t)] using hreal
  have hpow : taoGeom2CenteredExpMoment t ^ N ≤ Real.exp (3 * t ^ 2 * N) := by
    calc
      taoGeom2CenteredExpMoment t ^ N ≤ Real.exp (3 * t ^ 2) ^ N :=
        pow_le_pow_left₀ (taoGeom2CenteredExpMoment_nonneg t)
          (centeredMoment_le_exp_three_sq ht) N
      _ = Real.exp (3 * t ^ 2 * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  calc
    ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < t * taoGeom2CenteredListWeight as}).toReal ≤
      Real.exp (3 * t ^ 2 * N) / Real.exp lambda := by
        rw [le_div_iff₀ (Real.exp_pos _)]
        exact hmul.trans hpow
    _ = Real.exp (-lambda + 3 * t ^ 2 * N) := by
      rw [← Real.exp_sub]
      congr 1
      ring

theorem centeredList_absTail_le (N : ℕ) {t lambda : ℝ}
    (ht : 0 < t) (htsmall : t ≤ 1 / 4) (hlambda : 0 ≤ lambda) :
    ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      2 * Real.exp (-t * lambda + 3 * t ^ 2 * N) := by
  let Epos : Set (List ℕ+) := {as | lambda < taoGeom2CenteredListWeight as}
  let Eneg : Set (List ℕ+) := {as | taoGeom2CenteredListWeight as < -lambda}
  have hevent : {as | lambda < |taoGeom2CenteredListWeight as|} = Epos ∪ Eneg := by
    ext as
    simp only [Set.mem_setOf_eq, Set.mem_union, Epos, Eneg]
    constructor
    · intro h
      rcases lt_abs.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact lt_abs.mpr (Or.inl h)
      · exact lt_abs.mpr (Or.inr (by linarith))
  have hfinite (E : Set (List ℕ+)) :
      (geom2PNatListPMF N).toOuterMeasure E ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF N).toOuterMeasure E ≤
          (geom2PNatListPMF N).toOuterMeasure Set.univ :=
        (geom2PNatListPMF N).toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := ((geom2PNatListPMF N).toOuterMeasure_apply_eq_one_iff
        Set.univ).2 (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hunion := MeasureTheory.measure_union_le
    (μ := (geom2PNatListPMF N).toOuterMeasure) Epos Eneg
  rw [← hevent] at hunion
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite Epos, hfinite Eneg⟩) hunion
  rw [ENNReal.toReal_add (hfinite Epos) (hfinite Eneg)] at hreal
  have hp := centeredList_expTail_le N (t := t) (lambda := t * lambda)
    (by rw [abs_of_pos ht]; exact htsmall)
  have hn := centeredList_expTail_le N (t := -t) (lambda := t * lambda)
    (by rw [abs_neg, abs_of_pos ht]; exact htsmall)
  have ep : {as | t * lambda < t * taoGeom2CenteredListWeight as} = Epos := by
    ext as
    simp only [Set.mem_setOf_eq, Epos]
    constructor <;> intro h
    · nlinarith
    · exact mul_lt_mul_of_pos_left h ht
  have en : {as | t * lambda < -t * taoGeom2CenteredListWeight as} = Eneg := by
    ext as
    simp only [Set.mem_setOf_eq, Eneg]
    constructor <;> intro h <;> nlinarith
  rw [ep] at hp
  rw [en] at hn
  have he : -(t * lambda) + 3 * (-t) ^ 2 * (N : ℝ) =
      -t * lambda + 3 * t ^ 2 * N := by ring
  rw [he] at hn
  have hep : -(t * lambda) + 3 * t ^ 2 * (N : ℝ) =
      -t * lambda + 3 * t ^ 2 * N := by ring
  rw [hep] at hp
  calc
    ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      ((geom2PNatListPMF N).toOuterMeasure Epos).toReal +
        ((geom2PNatListPMF N).toOuterMeasure Eneg).toReal := hreal
    _ ≤ 2 * Real.exp (-t * lambda + 3 * t ^ 2 * N) := by linarith

theorem centeredList_absTail_le_twelve {N : ℕ} (hN : 0 < N)
    {lambda : ℝ} (hlambda : 0 < lambda) (hsmall : lambda ≤ (3 / 2 : ℝ) * N) :
    ((geom2PNatListPMF N).toOuterMeasure
      {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      2 * Real.exp (-(lambda ^ 2) / (12 * (N : ℝ))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 < lambda / (6 * (N : ℝ)) := by positivity
  have htsmall : lambda / (6 * (N : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 6 * N)]
    nlinarith
  have htail := centeredList_absTail_le N ht htsmall hlambda.le
  have he : -(lambda / (6 * (N : ℝ))) * lambda +
      3 * (lambda / (6 * (N : ℝ))) ^ 2 * N =
      -(lambda ^ 2) / (12 * (N : ℝ)) := by
    field_simp [hNR.ne']
    ring
  rwa [he] at htail

end SyracuseReport
