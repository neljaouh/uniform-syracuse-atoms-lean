import SyracuseLaw
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.MonotoneConvergence


/-! Exact target propositions for the paper's main theorems.
These definitions are specifications, not proofs. CheckMainTheorems.lean
requires closed theorems of these types and rejects extra axioms.
-/
namespace SyracuseReport
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter

def FloorAt (c : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n), IsUnit r →
    c / (3 : ℝ) ^ n ≤ (syracuseLaw n r).toReal

def AtomFloorStatement : Prop := ∃ c : ℝ, 0 < c ∧ FloorAt c

/-- Indexed by `n = 0,1,...` for depths `n+1 = 1,2,...`. -/
noncomputable def leastAtom (n : ℕ) : ℝ :=
  sInf (Set.range (fun r : (ZMod (3 ^ (n + 1)))ˣ =>
    (syracuseLaw (n + 1) (r : ZMod (3 ^ (n + 1)))).toReal))

noncomputable def normalizedMinimum (n : ℕ) : ℝ := (3 : ℝ) ^ (n + 1) * leastAtom n

noncomputable def minimumExponent (n : ℕ) : ℝ :=
  -Real.log (leastAtom n) / ((n + 1 : ℕ) * Real.log 3)

/-- Full Theorem A, including the positive limit, relative asymptotic, and exponent. -/
def MainTheoremA : Prop :=
  AtomFloorStatement ∧ Antitone normalizedMinimum ∧
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ 3 / 2 ∧
      Tendsto normalizedMinimum atTop (𝓝 ell) ∧
      Tendsto (fun n => leastAtom n / (ell / (3 : ℝ) ^ (n + 1))) atTop (𝓝 1) ∧
      Tendsto minimumExponent atTop (𝓝 1)

instance three_prime : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable local instance : MeasurableSpace (PadicInt 3) := borel (PadicInt 3)

noncomputable def cylinder (n : ℕ) (r : ZMod (3 ^ n)) : Set (PadicInt 3) :=
  {x | PadicInt.toZModPow n x = r}

def IsSyracuseLimit (mu : Measure (PadicInt 3)) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ n r, mu (cylinder n r) = syracuseLaw n r

/-- Cylinder characterization of the Haar probability conditioned on units.
Existence and all measure-theoretic conclusions are obligations of Theorem B. -/
def IsUnitHaar (H : Measure (PadicInt 3)) : Prop :=
  IsProbabilityMeasure H ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
    H (cylinder n r) = if IsUnit r then ENNReal.ofReal ((3 / 2 : ℝ) / (3 : ℝ) ^ n) else 0

/-- Full Theorem B. The measures are constructed in the conclusion, not
supplied as assumptions by the caller. -/
def MainTheoremB : Prop :=
  ∃ (mu H : Measure (PadicInt 3)) (f : PadicInt 3 → ℝ) (ell : ℝ),
    IsSyracuseLimit mu ∧ IsUnitHaar H ∧ 0 < ell ∧
    Tendsto normalizedMinimum atTop (𝓝 ell) ∧
    Integrable f H ∧ (∀ᵐ x ∂H, 0 ≤ f x) ∧
    mu = H.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    essInf f H = (2 / 3 : ℝ) * ell ∧
    mu ≪ H ∧ H ≪ mu ∧
    ∀ c : ℝ, 0 < c → (FloorAt c ↔ ∀ᵐ x ∂H, (2 / 3 : ℝ) * c ≤ f x)

/-- The one-division integer Collatz map used in the report (both signs). -/
def collatz (m : ℤ) : ℤ := if m % 2 = 0 then m / 2 else (3 * m + 1) / 2

def Reaches (m a : ℤ) : Prop := ∃ j : ℕ, collatz^[j] m = a

noncomputable def predecessorCount (a : ℤ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc ⌈-x⌉ ⌊x⌋).filter (fun m => Reaches m a)).card

/-- Full Theorem C, with signed targets, every sufficiently large real
cutoff, and the logarithmic exponent limit. -/
def MainTheoremC : Prop :=
  ∀ a : ℤ, ¬3 ∣ a →
    (∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      x ^ (1 - eps) ≤ (predecessorCount a x : ℝ)) ∧
    Tendsto (fun x : ℝ => Real.log (predecessorCount a x) / Real.log x) atTop (𝓝 1)

end SyracuseReport
