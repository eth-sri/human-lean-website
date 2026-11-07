import Formalization.Result.helpers.Lemma_2p5.Machinery
import Formalization.Axioms
import Formalization.Result.Lemma_2p4

noncomputable section
namespace UnitDistance

/-- Lemma 2.5: injectivity and the count of unordered unit pairs. -/
theorem paper_2_5 {A : AdmissibleDatum} (W : MinkowskiWindow A)
    (H : ℝ) (hH : 0 < H) (hγ : 0 < translationGrowth A.t H)
    (hU : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L) ≤ (W.U.card : ℝ))
    (hunit : ∀ u ∈ W.U, ∀ σ : A.K →+* ℂ, ‖σ u‖ = 1)
    (hR : 1 / 2 < W.R)
    (hρ : -(translationGrowth A.t H) / 2 < Real.log (discOverlapRatio W.R))
    (a : Fin (Module.finrank ℚ A.L) → ℂ) (hN : 0 < windowPointCount W a)
    (hE : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L / 2) *
      windowPointCount W a ≤ (windowEdgeCount W a : ℝ)) :
    let X : Set (Fin (Module.finrank ℚ A.L) → ℂ) := {z |
      (∃ x : A.K, IsIntegral ℤ ((admissibleDenominator A : A.K) * x) ∧
        ∀ j, z j = a j + W.σ j x) ∧ ∀ j, ‖z j‖ ≤ W.R}
    X.Finite ∧
    Set.InjOn (fun z : Fin (Module.finrank ℚ A.L) → ℂ =>
      z ⟨0, Module.finrank_pos⟩) X ∧
    (windowProjection W a).Finite ∧
    Nat.card (windowProjection W a) = windowPointCount W a ∧
    (1 / 2 : ℝ) * Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L / 2) *
      Nat.card (windowProjection W a) ≤ (unitDistanceCount (windowProjection W a) : ℝ) := (by
  -- HumanLean:proof_begin
  exact (open Formalization.Result.helpers.Lemma_2p4.Machinery
    Formalization.Result.helpers.Lemma_2p5.Machinery in by
    classical
    let V := Fin (Module.finrank ℚ A.L) → ℂ
    let X : Set V := {z | (∃ x : A.K,
      IsIntegral ℤ ((admissibleDenominator A : A.K) * x) ∧
      ∀ j, z j = a j + W.σ j x) ∧ ∀ j, ‖z j‖ ≤ W.R}
    let j₀ : Fin (Module.finrank ℚ A.L) := ⟨0, Module.finrank_pos⟩
    let π : V → ℂ := fun z => z j₀
    -- Compactness and the fractional-ideal lattice give a finite window section.
    have hX : X.Finite := by
      let B : Set V := {z | ∀ j, ‖z j‖ ≤ W.R}
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
      obtain ⟨Λ, b, hΛ, hb, _⟩ := window_lattice W
      have heq : X = {z : V | z - a ∈ Submodule.span ℤ (Set.range b) ∧ z ∈ B} := by
        ext z
        rw [← hb]
        exact and_congr (window_coset_mem W Λ hΛ a z) Iff.rfl
      rw [heq]
      exact finite_coset_section b a hBc.isBounded
    -- Equal first coordinates cancel the translate; the field embedding is injective.
    have hπ : Set.InjOn π X := by
      intro z hz w hw heq
      obtain ⟨x, hx, hzx⟩ := hz.1
      obtain ⟨y, hy, hwy⟩ := hw.1
      have hxy : x = y := (W.σ j₀).injective (add_left_cancel
        ((hzx j₀).symm.trans (heq.trans (hwy j₀))))
      ext j
      rw [hzx j, hwy j, hxy]
    have hP : (windowProjection W a).Finite := hX.image π
    have hcard : Nat.card (windowProjection W a) = windowPointCount W a :=
      Nat.card_image_of_injOn hπ
    refine ⟨hX, hπ, hP, hcard, ?_⟩
    -- Projection maps selected edges injectively into ordered planar unit pairs.
    let E := {e : V × V // e.1 ∈ X ∧ e.2 ∈ X ∧
      ∃ u ∈ W.U, ∀ j, e.2 j - e.1 j = W.σ j u}
    let O := {e : ℂ × ℂ // e.1 ∈ windowProjection W a ∧
      e.2 ∈ windowProjection W a ∧ dist e.1 e.2 = 1}
    have hOf : Set.Finite {e : ℂ × ℂ | e.1 ∈ windowProjection W a ∧
        e.2 ∈ windowProjection W a ∧ dist e.1 e.2 = 1} :=
      (hP.prod hP).subset (fun _ h => ⟨h.1, h.2.1⟩)
    letI : Finite O := hOf.to_subtype
    let project (e : E) : O := ⟨(π e.val.1, π e.val.2), by
      refine ⟨⟨e.val.1, e.property.1, rfl⟩,
        ⟨e.val.2, e.property.2.1, rfl⟩, ?_⟩
      obtain ⟨u, hu, he⟩ := e.property.2.2
      change dist (e.val.1 j₀) (e.val.2 j₀) = 1
      rw [dist_eq_norm, norm_sub_rev, he j₀]
      exact hunit u hu (W.σ j₀)⟩
    have hproject : Function.Injective project := by
      intro e f h
      have hp := congrArg Subtype.val h
      exact Subtype.ext (Prod.ext
        (hπ e.property.1 f.property.1 (congrArg Prod.fst hp))
        (hπ e.property.2.1 f.property.2.1 (congrArg Prod.snd hp)))
    have hedge : windowEdgeCount W a ≤ 2 * unitDistanceCount (windowProjection W a) :=
      (Nat.card_le_card_of_injective project hproject).trans (ordered_unit_pairs_bound _ hP)
    -- Each unordered segment admits at most two orientations, even for nonsymmetric U.
    have hedgeR : (windowEdgeCount W a : ℝ) ≤
        2 * (unitDistanceCount (windowProjection W a) : ℝ) := by exact_mod_cast hedge
    rw [hcard]
    nlinarith [hE])
  -- HumanLean:proof_end
)
end UnitDistance
