import TerminalBandTransport
set_option backward.isDefEq.respectTransparency false

/-! Actual finite admissible families obtained by pruning the manuscript's
selected prefixes. Noncontributing words are removed without changing mass.
The remaining quantitative target is a positive lower mass, uniform in all
roots of one fixed cylinder and in every sufficiently large word length. -/

namespace SyracuseReport
open scoped BigOperators

noncomputable def contributingPrunedPrefixes (N t m : ℕ) (R : ℤ) : Finset Word := by
  classical
  exact (terminalPrunedPrefixes N t m).filter (fun w => Contributes w R)

theorem contributingPrunedPrefixes_mass (N t m : ℕ) (R : ℤ) :
    (∑ w ∈ contributingPrunedPrefixes N t m R, wordTransport w 0 R (density 0)) =
      ∑ w ∈ terminalPrunedPrefixes N t m, wordTransport w 0 R (density 0) := by
  classical
  rw [contributingPrunedPrefixes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hc : Contributes w R
  · simp only [hc, ite_true]
  · simp only [hc, ite_false, wordTransport, if_neg hc]

theorem contributingPrunedPrefixes_properties (N t m : ℕ) (R : ℤ)
    (ht : t ≤ 2 * blockLength N) :
    (∀ w ∈ contributingPrunedPrefixes N t m R,
      w.length = prefixDepth N + t ∧ Contributes w R ∧
      w.beta ≤ (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength ∧
      2 * (prefixDepth N + t) ≤ w.total + (prefixWindow N + m) ∧
      w.total ≤ 2 * (prefixDepth N + t) + (prefixWindow N + m)) ∧
    ((contributingPrunedPrefixes N t m R).image Word.total).card ≤
      2 * (prefixWindow N + m) + 1 := by
  classical
  constructor
  · intro w hw
    obtain ⟨hw', hc⟩ := Finset.mem_filter.mp hw
    exact ⟨terminalPrunedPrefixes_length hw', hc,
      terminalPrunedPrefixes_beta_bound ht hw', terminalPrunedPrefixes_total_bounds hw'⟩
  · apply (Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun w => Contributes w R) (terminalPrunedPrefixes N t m)))).trans
    exact terminalPrunedPrefixes_total_image_card N t m

/-- This target concerns the actual selected/pruned families, at every
sufficiently large word length. It is not an added axiom or a closed paper
endpoint: its proof must come from the selected construction and the
vanishing flexible-comparison and terminal-pruning errors. -/
def ActualBalancedCylinderFamilies : Prop :=
  ∃ (q : ℕ) (b : ZMod (3 ^ q)) (kappa : ℝ),
    1 ≤ q ∧ IsUnit b ∧ 0 < kappa ∧
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
      ∃ H : ℕ, ∀ h : ℕ, H ≤ h → ∀ R : ℤ, (R : ZMod (3 ^ q)) = b →
        ∃ N t m : ℕ, h = prefixDepth N + t ∧ t ≤ 2 * blockLength N ∧
          (prefixWindow N + m : ℝ) ≤ delta * (h : ℝ) ∧
          kappa ≤ ∑ w ∈ terminalPrunedPrefixes N t m,
            wordTransport w 0 R (density 0)

/-- The actual positive-mass target gives a finite balanced admissible
family with bounded offset and only linearly many possible total valuations. -/
theorem balanced_word_families_of_actual (hactual : ActualBalancedCylinderFamilies) :
    ∃ (q : ℕ) (b : ZMod (3 ^ q)) (kappa B : ℝ),
      1 ≤ q ∧ IsUnit b ∧ 0 < kappa ∧ 0 < B ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
        ∃ H : ℕ, ∀ h : ℕ, H ≤ h → ∀ R : ℤ, (R : ZMod (3 ^ q)) = b →
          ∃ V : Finset Word,
            (∀ w ∈ V, w.length = h ∧ Contributes w R ∧ w.beta ≤ B ∧
              2 * (h : ℝ) - delta * (h : ℝ) ≤ (w.total : ℝ) ∧
              (w.total : ℝ) ≤ 2 * (h : ℝ) + delta * (h : ℝ)) ∧
            (V.image Word.total).card ≤ 2 * h + 1 ∧
            kappa ≤ ∑ w ∈ V, wordTransport w 0 R (density 0) := by
  classical
  obtain ⟨q, b, kappa, hq, hb, hkappa, hfamilies⟩ := hactual
  let B : ℝ := (2 : ℝ) ^ (baseBlockLength + 1) + (16 : ℝ) ^ baseBlockLength
  refine ⟨q, b, kappa, B, hq, hb, hkappa, by dsimp [B]; positivity, ?_⟩
  intro delta hdelta hsmall
  obtain ⟨H, hH⟩ := hfamilies delta hdelta hsmall
  refine ⟨H, ?_⟩
  intro h hh R hR
  obtain ⟨N, t, m, hlen, ht, hwindow, hmass⟩ := hH h hh R hR
  have hprops := contributingPrunedPrefixes_properties N t m R ht
  refine ⟨contributingPrunedPrefixes N t m R, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwlen, hc, hbeta, hlo, hhi⟩ := hprops.1 w hw
    rw [← hlen] at hwlen hlo hhi
    have hloR : 2 * (h : ℝ) ≤ (w.total : ℝ) + (prefixWindow N + m : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (w.total : ℝ) ≤ 2 * (h : ℝ) + (prefixWindow N + m : ℝ) := by
      exact_mod_cast hhi
    exact ⟨hwlen, hc, hbeta, by linarith, by linarith⟩
  · have hhR : (0 : ℝ) ≤ h := by positivity
    have hsmallR := mul_le_mul_of_nonneg_right hsmall hhR
    have hwindowNat : prefixWindow N + m ≤ h := by
      have hr : (prefixWindow N + m : ℝ) ≤ (h : ℝ) := by linarith
      exact_mod_cast hr
    exact hprops.2.trans (by omega)
  · rw [contributingPrunedPrefixes_mass]
    exact hmass

end SyracuseReport
