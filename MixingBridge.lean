import LawIdentification
import PaperStatements
import Erdos1135.Tao.Fourier.Prop114CanonicalAssembly
import Erdos1135.Tao.Section6.AdjacentOneStep

namespace SyracuseReport
open scoped BigOperators

theorem density_difference_eq_scaled_mass {m n : ℕ} (hmn : m ≤ n)
    (r : ZMod (3 ^ n)) :
    density n r - density m (residueProjection hmn r) =
      ((2 / 3 : ℝ) * (3 : ℝ) ^ n) *
        (Erdos1135.Tao.syracPMFMassVector n r -
          Erdos1135.Tao.taoZModPowUniformLift hmn
            (Erdos1135.Tao.syracPMFMassVector m) r) := by
  simp only [density, syracuseLaw_eq_syracPMF]
  unfold Erdos1135.Tao.syracPMFMassVector Erdos1135.Tao.taoZModPowUniformLift
    Erdos1135.Tao.zmodPowFiberAverageScale
  rw [residueProjection_eq_reference]
  push_cast
  field_simp

theorem finiteMean_density_difference {m n : ℕ} (hmn : m ≤ n) :
    finiteMean (fun r : ZMod (3 ^ n) =>
      |density n r - density m (residueProjection hmn r)|) =
      (2 / 3 : ℝ) * Erdos1135.Tao.syracFineScaleOscillation m n := by
  rw [Erdos1135.Tao.syracFineScaleOscillation_eq_sum_abs_sub_uniformLift hmn]
  have habs (r : ZMod (3 ^ n)) :
      |density n r - density m (residueProjection hmn r)| =
        ((2 / 3 : ℝ) * (3 : ℝ) ^ n) *
          |Erdos1135.Tao.syracPMFMassVector n r -
            Erdos1135.Tao.taoZModPowUniformLift hmn
              (Erdos1135.Tao.syracPMFMassVector m) r| := by
    rw [density_difference_eq_scaled_mass hmn, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 / 3) * 3 ^ n)]
  unfold finiteMean
  simp_rw [habs]
  rw [← Finset.mul_sum, ZMod.card]
  push_cast
  field_simp

theorem paper_thm_mixing : PaperStatements.thm_mixing := by
  intro A hA
  obtain ⟨C, hC, hmix⟩ := Erdos1135.Tao.taoProp114FineScaleMixing A hA
  refine ⟨C, hC, ?_⟩
  intro n m hm hmn
  rw [finiteMean_density_difference hmn]
  calc
    _ ≤ (2 / 3 : ℝ) * (C / (m : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left (hmix n m hm hmn) (by norm_num)
    _ = _ := by ring

end SyracuseReport
