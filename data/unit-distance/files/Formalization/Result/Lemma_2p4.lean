import Formalization.Result.helpers.Lemma_2p4.Machinery
import Formalization.Axioms
import Formalization.Result.Proposition_2p2

noncomputable section
namespace UnitDistance

/-- Lemma 2.4, with nonempty referring to the window section. -/
theorem paper_2_4 {A : AdmissibleDatum} (W : MinkowskiWindow A)
    (H : ℝ) (hH : 0 < H) (hγ : 0 < translationGrowth A.t H)
    (hU : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L) ≤ (W.U.card : ℝ))
    (hunit : ∀ u ∈ W.U, ∀ σ : A.K →+* ℂ, ‖σ u‖ = 1)
    (hR : 1 / 2 < W.R)
    (hρ : -(translationGrowth A.t H) / 2 < Real.log (discOverlapRatio W.R)) :
    ∃ a : Fin (Module.finrank ℚ A.L) → ℂ,
      0 < windowPointCount W a ∧
      Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L / 2) *
        windowPointCount W a ≤ (windowEdgeCount W a : ℝ) := (by
  -- HumanLean:proof_begin
  exact (open Formalization.Result.helpers.Lemma_2p4.Machinery in by
    classical
    let V := Fin (Module.finrank ℚ A.L) → ℂ
    let B : Set V := {z | ∀ j, ‖z j‖ ≤ W.R}
    let Φ : A.K → V := fun x j => W.σ j x
    have hΦ : Function.Injective Φ := by
      intro x y h
      exact (W.σ ⟨0, Module.finrank_pos⟩).injective
        (congrFun h ⟨0, Module.finrank_pos⟩)
    have hR0 : 0 < W.R := by linarith
    have hBc : IsCompact B := by
      have hset : B = Set.pi Set.univ (fun _ : Fin (Module.finrank ℚ A.L) =>
          Metric.closedBall (0 : ℂ) W.R) := by
        ext z
        constructor
        · intro hz j _
          exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hz j)
        · intro hz j
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz j (Set.mem_univ j)
      rw [hset]
      exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
    -- The fractional-ideal lattice supplies the bounded fundamental domain.
    obtain ⟨Λ, b, hΛ, hb, T, hTm, hTb, hT, hTpos, hTfinite⟩ := window_lattice W
    letI : Countable Λ := by rw [hb]; infer_instance
    let X : V → Set V := fun a => {z | z - a ∈ Λ ∧ z ∈ B}
    have hX : ∀ a, (X a).Finite := by
      intro a
      simpa only [X, hb] using finite_coset_section b a hBc.isBounded
    have hN : ∀ a, windowPointCount W a = Nat.card (X a) := by
      intro a
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun z =>
        and_congr (window_coset_mem W Λ hΛ a z) Iff.rfl)
    have hUs : ∀ u ∈ W.U, Φ u ∈ Λ := by
      intro u hu
      exact (hΛ _).mpr ⟨u, W.integral_translations u hu, fun _ => rfl⟩
    have hE : ∀ a, windowEdgeCount W a =
        ∑ u : W.U, Nat.card {z : V // z - a ∈ Λ ∧ z ∈ B ∧ z + Φ u ∈ B} := by
      intro a
      calc
        windowEdgeCount W a = Nat.card {e : V × V //
            e.1 ∈ X a ∧ e.2 ∈ X a ∧ ∃ u ∈ W.U, e.2 - e.1 = Φ u} := by
          apply Nat.card_congr
          apply Equiv.subtypeEquivRight
          intro e
          simp only [X, B, Set.mem_setOf_eq, window_coset_mem W Λ hΛ, Φ]
          exact and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun u =>
            and_congr Iff.rfl ⟨fun h => funext h, fun h => congrFun h⟩))
        _ = ∑ u : W.U, Nat.card {z : V // z ∈ X a ∧ z + Φ u ∈ X a} :=
          ordered_edge_count (X a) (hX a) W.U Φ hΦ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u _
          apply Nat.card_congr
          apply Equiv.subtypeEquivRight
          intro z
          constructor
          · rintro ⟨hz, hz'⟩
            exact ⟨hz.1, hz.2, hz'.2⟩
          · rintro ⟨hz, hzB, hzB'⟩
            refine ⟨⟨hz, hzB⟩, ?_, hzB'⟩
            have heq : z + Φ u - a = (z - a) + Φ u := by abel
            rw [heq]
            exact Λ.add_mem hz (hUs u u.property)
    -- Unfolding the window indicator gives its positive mean.
    have hNI : MeasureTheory.Integrable (fun a => (windowPointCount W a : ℝ))
        (MeasureTheory.volume.restrict T) ∧
        (∫ a in T, (windowPointCount W a : ℝ)) = (Real.pi * W.R ^ 2) ^ Module.finrank ℚ A.L := by
      have hc : (fun a => (windowPointCount W a : ℝ)) =
          (fun a => (∑' l : Λ, B.indicator (fun _ => (1 : ENNReal))
            ((l : V) + a)).toReal) := by
        funext a
        rw [hN a]
        exact coset_count_eq_indicator_sum Λ a B
      rw [hc]
      obtain ⟨hi, heq⟩ := unfold_window_indicator Λ hT hBc.measurableSet hBc.measure_lt_top.ne
      exact ⟨hi, heq.trans (polydisc_volume _ hR0.le)⟩
    -- For each translation, ordered pairs are points in the overlap window.
    -- Unit coordinate lengths make every overlap volume the same product.
    have hEI : MeasureTheory.Integrable (fun a => (windowEdgeCount W a : ℝ))
        (MeasureTheory.volume.restrict T) ∧
        (∫ a in T, (windowEdgeCount W a : ℝ)) = (W.U.card : ℝ) *
          (MeasureTheory.volume (Metric.closedBall (0 : ℂ) W.R ∩
            Metric.closedBall 1 W.R)).toReal ^ Module.finrank ℚ A.L := by
      let S : W.U → Set V := fun u => {z | z ∈ B ∧ z + Φ u ∈ B}
      let C : W.U → V → ℝ := fun u a => (Nat.card {z : V // z - a ∈ Λ ∧ z ∈ S u} : ℝ)
      have hCi : ∀ u : W.U, MeasureTheory.Integrable (C u) (MeasureTheory.volume.restrict T) ∧
          (∫ a in T, C u a) = (MeasureTheory.volume (Metric.closedBall (0 : ℂ) W.R ∩
            Metric.closedBall 1 W.R)).toReal ^ Module.finrank ℚ A.L := by
        intro u
        have hSc : IsClosed (S u) := hBc.isClosed.inter
          (hBc.isClosed.preimage (continuous_id.add continuous_const))
        have hSf : MeasureTheory.volume (S u) ≠ ⊤ :=
          (lt_of_le_of_lt (MeasureTheory.measure_mono (fun _ hz => hz.1))
            hBc.measure_lt_top).ne
        have hc : C u = (fun a => (∑' l : Λ, (S u).indicator (fun _ => (1 : ENNReal))
            ((l : V) + a)).toReal) := by
          funext a
          exact coset_count_eq_indicator_sum Λ a (S u)
        rw [hc]
        obtain ⟨hi, heq⟩ := unfold_window_indicator Λ hT hSc.measurableSet hSf
        exact ⟨hi, heq.trans (polydisc_overlap_volume (Φ u)
          (fun j => W.unit_coordinates u u.property j) W.R)⟩
      have he : (fun a => (windowEdgeCount W a : ℝ)) = fun a => ∑ u : W.U, C u a := by
        funext a
        rw [hE a, Nat.cast_sum]
        rfl
      rw [he]
      refine ⟨MeasureTheory.integrable_finset_sum _ (fun u _ => (hCi u).1), ?_⟩
      rw [MeasureTheory.integral_finset_sum _ (fun u _ => (hCi u).1)]
      calc
        _ = ∑ _u : W.U, (MeasureTheory.volume (Metric.closedBall (0 : ℂ) W.R ∩
            Metric.closedBall 1 W.R)).toReal ^ Module.finrank ℚ A.L :=
          Finset.sum_congr rfl (fun u _ => (hCi u).2)
        _ = _ := by simp
    -- The mean ratio is |U| ρ^f, strictly above the required exponential.
    have hcoefficient : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L / 2) <
        (W.U.card : ℝ) * discOverlapRatio W.R ^ Module.finrank ℚ A.L :=
      exponential_overlap_bound Module.finrank_pos (overlap_positive hR) hρ hU
    have hmean : 0 < ∫ a in T, (windowPointCount W a : ℝ) := by
      rw [hNI.2]
      exact pow_pos (mul_pos Real.pi_pos (sq_pos_of_pos hR0)) _
    have hratio : (∫ a in T, (windowEdgeCount W a : ℝ)) =
        ((W.U.card : ℝ) * discOverlapRatio W.R ^ Module.finrank ℚ A.L) *
        ∫ a in T, (windowPointCount W a : ℝ) := by
      rw [hNI.2, hEI.2, discOverlapRatio, div_pow]
      have hn : (Real.pi * W.R ^ 2) ^ Module.finrank ℚ A.L ≠ 0 :=
        ne_of_gt (pow_pos (mul_pos Real.pi_pos (sq_pos_of_pos hR0)) _)
      field_simp
    have hempty : ∀ a, (windowPointCount W a : ℝ) = 0 → (windowEdgeCount W a : ℝ) = 0 := by
      intro a hn
      have hn' : Nat.card (X a) = 0 := by exact_mod_cast (by rwa [hN a] at hn : (Nat.card (X a) : ℝ) = 0)
      letI : Finite (X a) := (hX a).to_subtype
      have hxempty : IsEmpty (X a) := (Nat.card_eq_zero.mp hn').resolve_right (not_infinite_iff_finite.mpr inferInstance)
      have hnone : ∀ z, z ∉ X a := fun z hz => hxempty.false ⟨z, hz⟩
      rw [hE a]
      have hz : ∀ u : W.U, Nat.card {z : V // z - a ∈ Λ ∧ z ∈ B ∧ z + Φ u ∈ B} = 0 := by
        intro u
        letI : IsEmpty {z : V // z - a ∈ Λ ∧ z ∈ B ∧ z + Φ u ∈ B} :=
          ⟨fun z => hnone z ⟨z.property.1, z.property.2.1⟩⟩
        exact Nat.card_of_isEmpty
      simp [hz]
    obtain ⟨a, ha, he⟩ := select_from_integral_ratio (MeasureTheory.volume.restrict T)
      (fun a => (windowPointCount W a : ℝ)) (fun a => (windowEdgeCount W a : ℝ))
      _ _ hNI.1 hEI.1 (fun _ => Nat.cast_nonneg _) hempty hmean hratio hcoefficient
    exact ⟨a, by exact_mod_cast ha, he⟩)
  -- HumanLean:proof_end
)
end UnitDistance
