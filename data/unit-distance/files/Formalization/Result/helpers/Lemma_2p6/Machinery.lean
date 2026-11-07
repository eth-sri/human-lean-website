import Formalization.Axioms
import Formalization.Definition
import Formalization.Result.Proposition_2p2
import Formalization.Result.Lemma_2p4
import Formalization.Result.Lemma_2p5
import Mathlib

namespace Formalization.Result.helpers.Lemma_2p6.Machinery



/-- Disjoint balls in a larger ball give the usual finite packing estimate. -/
lemma packing_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) (R δ : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * δ ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ ((R + δ) / δ) ^ Module.finrank ℝ E := by
  classical
  borelize E
  let μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar
  have hρ : 0 < R + δ := add_pos_of_nonneg_of_pos hR hδ
  have hd : Set.Pairwise (s : Set E)
      (fun x y => Disjoint (Metric.ball x δ) (Metric.ball y δ)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [two_mul] using hsep x hx y hy hxy
  have hsub : (⋃ x ∈ s, Metric.ball x δ) ⊆ Metric.ball (0 : E) (R + δ) := by
    refine Set.iUnion₂_subset fun x hx => Metric.ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs x hx]
  have hvol : (s.card : ENNReal) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) *
      μ (Metric.ball 0 1) ≤
      ENNReal.ofReal ((R + δ) ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) := by
    calc
      _ = μ (⋃ x ∈ s, Metric.ball x δ) := by
        rw [MeasureTheory.measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball 0 (R + δ)) := MeasureTheory.measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos μ (0 : E) zero_lt_one).ne'
    MeasureTheory.measure_ball_lt_top.ne).mp hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (pow_nonneg hρ.le (Module.finrank ℝ E)) hcancel
  have hreal' : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤
      (R + δ) ^ Module.finrank ℝ E := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using hreal
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr hreal'



end Formalization.Result.helpers.Lemma_2p6.Machinery
