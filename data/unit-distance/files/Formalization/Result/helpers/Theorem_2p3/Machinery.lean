import Formalization.Axioms
import Formalization.Definition
import Formalization.Result.Proposition_2p2
import Formalization.Result.Lemma_2p4
import Formalization.Result.Lemma_2p5
import Formalization.Result.Lemma_2p6
import Mathlib

namespace Formalization.Result.helpers.Theorem_2p3.Machinery



lemma overlap_lower_bound {R : ℝ} (hR : 1 ≤ R) :
    (1 - 1 / R) ^ 2 ≤ UnitDistance.discOverlapRatio R := by
  have hR0 : 0 < R := by linarith
  have hs : Metric.closedBall (0 : ℂ) (R - 1) ⊆
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R := by
    intro z hz
    have hz' := Metric.mem_closedBall.mp hz
    constructor
    · exact Metric.mem_closedBall.mpr (by linarith)
    · exact Metric.mem_closedBall.mpr (by
        have ht := dist_triangle z (0 : ℂ) 1
        norm_num at ht
        simp only [dist_zero_right] at hz'
        linarith)
  have hf : MeasureTheory.volume
      (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  have hv := ENNReal.toReal_mono hf (MeasureTheory.measure_mono hs)
  simp [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - 1)] at hv
  unfold UnitDistance.discOverlapRatio
  apply (le_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hR0))).mpr
  have he : (1 - 1 / R) ^ 2 * (Real.pi * R ^ 2) = (R - 1) ^ 2 * Real.pi := by
    field_simp
    <;> ring
  rw [he]
  exact hv

lemma exists_uniform_radius {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : ℝ, 1 ≤ R ∧ -γ / 2 < Real.log (UnitDistance.discOverlapRatio R) := by
  have ht : Filter.Tendsto (fun R : ℝ => (1 - 1 / R) ^ 2)
      Filter.atTop (nhds 1) := by
    simpa only [one_div, sub_zero, one_pow] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_inv_atTop_zero : Filter.Tendsto (fun R : ℝ => R⁻¹) _ _)).pow 2
  have he : Real.exp (-γ / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hev := ht.eventually (lt_mem_nhds he)
  obtain ⟨R, hR, hlarge⟩ := (Filter.eventually_ge_atTop (1 : ℝ)).and hev |>.exists
  have hl := lt_of_lt_of_le hlarge (overlap_lower_bound hR)
  exact ⟨R, hR, (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hl)).mpr hl⟩

lemma exists_embedding_family (A : UnitDistance.AdmissibleDatum) :
    ∃ σ : Fin (Module.finrank ℚ A.L) → (A.K →+* ℂ),
      Function.Bijective (fun j => (σ j).comp (algebraMap A.L A.K)) := by
  classical
  let e : Fin (Module.finrank ℚ A.L) ≃ (A.L →+* ℂ) :=
    Fintype.equivOfCardEq (by simp [NumberField.Embeddings.card])
  have hx : ∀ j, ∃ σ : A.K →+* ℂ, σ.comp (algebraMap A.L A.K) = e j := by
    intro j
    obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ) (L := A.L) (M := ℂ) (E := A.K) (e j).toRatAlgHom
    exact ⟨σ.toRingHom, congrArg AlgHom.toRingHom hσ⟩
  choose σ hσ using hx
  exact ⟨σ, by simpa only [hσ] using e.bijective⟩

lemma denominator_eq {A B : UnitDistance.AdmissibleDatum}
    (ht : A.t = B.t) (hq : HEq A.q B.q) :
    UnitDistance.admissibleDenominator A = UnitDistance.admissibleDenominator B := by
  have hp {t s : ℕ} (h : t = s) (q : Fin t → ℕ) (r : Fin s → ℕ)
      (hr : HEq q r) : (∏ b, q b) = ∏ b, r b := by
    subst s
    cases hr
    rfl
  exact congrArg (fun n : ℕ => n ^ 2) (hp ht A.q B.q hq)


lemma ordered_edges_le_square {A : UnitDistance.AdmissibleDatum}
    (W : UnitDistance.MinkowskiWindow A) (a : Fin (Module.finrank ℚ A.L) → ℂ)
    (hX : Set.Finite {z : Fin (Module.finrank ℚ A.L) → ℂ |
      (∃ x : A.K, IsIntegral ℤ ((UnitDistance.admissibleDenominator A : A.K) * x) ∧
        ∀ j, z j = a j + W.σ j x) ∧ ∀ j, ‖z j‖ ≤ W.R}) :
    UnitDistance.windowEdgeCount W a ≤ UnitDistance.windowPointCount W a ^ 2 := by
  classical
  let X := {z : Fin (Module.finrank ℚ A.L) → ℂ |
      (∃ x : A.K, IsIntegral ℤ ((UnitDistance.admissibleDenominator A : A.K) * x) ∧
        ∀ j, z j = a j + W.σ j x) ∧ ∀ j, ‖z j‖ ≤ W.R}
  letI : Finite X := hX.to_subtype
  unfold UnitDistance.windowEdgeCount UnitDistance.windowPointCount
  change Nat.card {e : _ × _ // e.1 ∈ X ∧ e.2 ∈ X ∧ _} ≤ Nat.card X ^ 2
  calc
    _ ≤ Nat.card (X × X) := Nat.card_le_card_of_injective
      (fun e => (⟨e.val.1, e.property.1⟩, ⟨e.val.2, e.property.2.1⟩))
      (by intro e f h; exact Subtype.ext (congrArg (fun p : X × X => (p.1.val, p.2.val)) h))
    _ = _ := by rw [Nat.card_prod, pow_two]

lemma unit_count_le_powerset (P : Finset ℂ) :
    UnitDistance.unitDistanceCount (P : Set ℂ) ≤ 2 ^ P.card := by
  classical
  unfold UnitDistance.unitDistanceCount
  calc
    _ ≤ Nat.card ↥P.powerset := Nat.card_le_card_of_injective
      (fun s => (⟨s.val, Finset.mem_powerset.mpr (by
        intro x hx
        exact s.property.1 hx)⟩ : ↥P.powerset))
      (by intro s t h; exact Subtype.ext (congrArg (fun v : ↥P.powerset => v.val) h))
    _ = _ := by rw [Nat.card_eq_finsetCard, Finset.card_powerset]

lemma count_le_maximum (P : Set ℂ) (hP : P.Finite) :
    UnitDistance.unitDistanceCount P ≤ UnitDistance.unitDistanceMaximum (Nat.card P) := by
  classical
  apply le_csSup
  · refine ⟨2 ^ Nat.card P, ?_⟩
    rintro k ⟨Q, hQ, rfl⟩
    exact hQ ▸ unit_count_le_powerset Q
  · refine ⟨hP.toFinset, ?_, ?_⟩
    · exact (Nat.card_eq_card_finite_toFinset hP).symm
    · simp



end Formalization.Result.helpers.Theorem_2p3.Machinery
