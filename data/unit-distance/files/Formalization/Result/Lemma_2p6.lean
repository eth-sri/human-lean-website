import Formalization.Result.helpers.Lemma_2p6.Machinery
import Formalization.Axioms
import Formalization.Result.Lemma_2p5

noncomputable section
namespace UnitDistance

/-- Lemma 2.6, in the standing Section 2 setup. -/
theorem paper_2_6 {A : AdmissibleDatum} (W : MinkowskiWindow A)
    (H : ℝ) (hH : 0 < H) (hγ : 0 < translationGrowth A.t H)
    (hU : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L) ≤ (W.U.card : ℝ))
    (hunit : ∀ u ∈ W.U, ∀ σ : A.K →+* ℂ, ‖σ u‖ = 1)
    (hR : 1 / 2 < W.R)
    (hρ : -(translationGrowth A.t H) / 2 < Real.log (discOverlapRatio W.R))
    (a : Fin (Module.finrank ℚ A.L) → ℂ) (hN : 0 < windowPointCount W a)
    (hE : Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L / 2) *
      windowPointCount W a ≤ (windowEdgeCount W a : ℝ)) :
    (Nat.card (windowProjection W a) : ℝ) ≤
      Real.exp (2 * Real.log (4 * W.R * admissibleDenominator A) * Module.finrank ℚ A.L) := (by
  -- HumanLean:proof_begin
  exact (open Formalization.Result.helpers.Lemma_2p4.Machinery
    Formalization.Result.helpers.Lemma_2p6.Machinery in by
    classical
    let V := Fin (Module.finrank ℚ A.L) → ℂ
    let X : Set V := {z | (∃ x : A.K,
      IsIntegral ℤ ((admissibleDenominator A : A.K) * x) ∧
      ∀ j, z j = a j + W.σ j x) ∧ ∀ j, ‖z j‖ ≤ W.R}
    -- Lemma 2.5 identifies the projected cardinality with the finite window section.
    obtain ⟨hX, _, _, hcard, _⟩ := paper_2_5 W H hH hγ hU hunit hR hρ a hN hE
    change X.Finite at hX
    let D : ℝ := admissibleDenominator A
    have hD : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos A
    have hD1 : 1 ≤ D := by
      dsimp [D]
      exact_mod_cast (denominator_pos A)
    have hDK : (admissibleDenominator A : A.K) ≠ 0 := by
      exact_mod_cast (denominator_pos A).ne'
    let δ : ℝ := 1 / (2 * D)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hR0 : 0 ≤ W.R := by linarith
    -- The nonzero integral difference has a conjugate of modulus at least one,
    -- by the integral norm product. Conjugate pairs give a selected coordinate.
    have hsep : ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 2 * δ ≤ ‖z - w‖ := by
      intro z hz w hw hzw
      obtain ⟨x, hx, hzx⟩ := hz.1
      obtain ⟨y, hy, hwy⟩ := hw.1
      have hxy : x ≠ y := by
        intro he
        apply hzw
        funext j
        rw [hzx j, hwy j, he]
      let β : NumberField.RingOfIntegers A.K := ⟨(admissibleDenominator A : A.K) * (x - y), by
        rw [mul_sub]
        exact hx.sub hy⟩
      have hβ : β ≠ 0 := by
        intro he
        have he' := congrArg (fun v : NumberField.RingOfIntegers A.K => (v : A.K)) he
        exact (mul_ne_zero hDK (sub_ne_zero.mpr hxy)) he'
      obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hβ
      obtain ⟨⟨j, b⟩, hj⟩ := (embedding_pairs W).surjective σ
      have hjβ : 1 ≤ ‖W.σ j (β : A.K)‖ := by
        rw [← hj] at hσ
        cases b <;> simpa using hσ
      have hcoord : 1 ≤ D * ‖(z - w) j‖ := by
        have he : (z - w) j = W.σ j (x - y) := by
          change z j - w j = W.σ j (x - y)
          rw [hzx j, hwy j, map_sub]
          abel
        rw [he]
        simpa [β, map_mul, norm_mul, D] using hjβ
      have hsmall : 1 / D ≤ ‖(z - w) j‖ :=
        (div_le_iff₀ hD).mpr (by nlinarith [hcoord])
      have hrad : 2 * δ = 1 / D := by dsimp [δ]; field_simp
      rw [hrad]
      exact hsmall.trans (norm_le_pi_norm (z - w) j)
    -- Radius 1/(2D) sup-norm balls are disjoint and lie in radius R+1/(2D).
    have hpack := packing_bound hX.toFinset W.R δ hδ hR0
      (fun z hz => (pi_norm_le_iff_of_nonneg hR0).mpr
        (hX.mem_toFinset.mp hz).2)
      (fun z hz w hw hzw => hsep z (hX.mem_toFinset.mp hz)
        w (hX.mem_toFinset.mp hw) hzw)
    have hc : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
    have hdim : Module.finrank ℝ V = 2 * Module.finrank ℚ A.L := by
      change Module.finrank ℝ (Fin (Module.finrank ℚ A.L) → ℂ) = _
      rw [Module.finrank_pi_fintype]
      simp only [hc, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    have hratio : (W.R + δ) / δ = 1 + 2 * W.R * D := by
      dsimp [δ]
      field_simp
      ring
    change (hX.toFinset.card : ℝ) ≤ ((W.R + δ) / δ) ^ Module.finrank ℝ V at hpack
    simp only [hdim, hratio] at hpack
    have hcount : hX.toFinset.card = windowPointCount W a := by
      change hX.toFinset.card = Nat.card X
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card X hX]
    rw [hcount] at hpack
    -- Here D ≥ 1 and R > 1/2 ensure 1+2RD ≤ 4RD.
    have hRD : 1 ≤ 2 * W.R * D := by nlinarith
    have hbase : 0 < 4 * W.R * D := by positivity
    have hpow : (1 + 2 * W.R * D) ^ (2 * Module.finrank ℚ A.L) ≤
        (4 * W.R * D) ^ (2 * Module.finrank ℚ A.L) := by
      gcongr
      linarith
    rw [hcard]
    refine hpack.trans (hpow.trans_eq ?_)
    rw [show 2 * Real.log (4 * W.R * admissibleDenominator A) *
        (Module.finrank ℚ A.L : ℝ) =
        Real.log (4 * W.R * D) * (2 * Module.finrank ℚ A.L : ℕ) by
          dsimp [D]; push_cast; ring]
    rw [mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log hbase])
  -- HumanLean:proof_end
)
end UnitDistance
