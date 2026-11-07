import Formalization.Result.helpers.Theorem_2p3.Machinery
import Formalization.Definition
import Formalization.Result.Proposition_2p2
import Formalization.Result.Lemma_2p4
import Formalization.Result.Lemma_2p5
import Formalization.Result.Lemma_2p6

noncomputable section
namespace UnitDistance

/-- Theorem 2.3: the geometric conclusion from a sequence of admissible data. -/
theorem paper_2_3 (A : ℕ → AdmissibleDatum)
    (hprimes : ∀ j, (A j).t = (A 0).t ∧ HEq (A j).q (A 0).q)
    (hdegree : Filter.Tendsto (fun j => Module.finrank ℚ (A j).L) Filter.atTop Filter.atTop)
    (H : ℝ) (hH : 0 < H)
    (hh : ∀ j, (classNumber (A j).K : ℝ) ≤ H ^ Module.finrank ℚ (A j).L)
    (hγ : 0 < translationGrowth (A 0).t H) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Infinite {n : ℕ |
      0 < n ∧ (n : ℝ) ^ (1 + δ) ≤ (unitDistanceMaximum n : ℝ)} := (by
  -- HumanLean:proof_begin
  exact (open Formalization.Result.helpers.Theorem_2p3.Machinery
    Formalization.Result.helpers.Lemma_2p4.Machinery in by
    classical
    let γ := translationGrowth (A 0).t H
    let f : ℕ → ℕ := fun j => Module.finrank ℚ (A j).L
    have hγj : ∀ j, translationGrowth (A j).t H = γ := by
      intro j
      dsimp [γ]
      rw [(hprimes j).1]
    -- Choose the radius and denominator before choosing any member of the sequence.
    obtain ⟨R, hR1, hρ⟩ := exists_uniform_radius hγ
    have hR : 1 / 2 < R := by linarith
    let D : ℝ := admissibleDenominator (A 0)
    have hD1 : 1 ≤ D := by
      dsimp [D]
      exact_mod_cast (denominator_pos (A 0))
    have hDj : ∀ j, (admissibleDenominator (A j) : ℝ) = D := by
      intro j
      dsimp [D]
      exact_mod_cast denominator_eq (hprimes j).1 (hprimes j).2
    let B := 2 * Real.log (4 * R * D)
    have hB : 0 < B := by
      have hRD : 1 < 4 * R * D := by nlinarith
      exact mul_pos (by norm_num) (Real.log_pos hRD)
    -- Proposition 2.2, followed by the averaging, projection and packing lemmas.
    have hsets : ∀ j, ∃ P : Set ℂ, P.Finite ∧ 0 < Nat.card P ∧
        Real.exp (γ * f j / 2) ≤ (Nat.card P : ℝ) ∧
        (Nat.card P : ℝ) ≤ Real.exp (B * f j) ∧
        (1 / 2 : ℝ) * Real.exp (γ * f j / 2) * Nat.card P ≤
          (unitDistanceCount P : ℝ) := by
      intro j
      obtain ⟨U, hUi, _, hunit, hU⟩ := paper_2_2 (A j) H hH (hh j)
      obtain ⟨σ, hσ⟩ := exists_embedding_family (A j)
      let W : MinkowskiWindow (A j) :=
        ⟨σ, hσ, U, hUi, fun u hu k => hunit u hu (σ k), R⟩
      have hγ' : 0 < translationGrowth (A j).t H := by rwa [hγj]
      have hρ' : -(translationGrowth (A j).t H) / 2 <
          Real.log (discOverlapRatio W.R) := by simpa [W, hγj] using hρ
      obtain ⟨a, hN, hE⟩ := paper_2_4 W H hH hγ' hU hunit hR hρ'
      obtain ⟨hX, _, hP, hc, hcount⟩ := paper_2_5 W H hH hγ' hU hunit hR hρ' a hN hE
      have hpack := paper_2_6 W H hH hγ' hU hunit hR hρ' a hN hE
      have hedge := ordered_edges_le_square W a hX
      have hlow : Real.exp (γ * f j / 2) ≤ (Nat.card (windowProjection W a) : ℝ) := by
        rw [hc]
        have hNr : (0 : ℝ) < windowPointCount W a := by exact_mod_cast hN
        have hsq : (windowEdgeCount W a : ℝ) ≤ (windowPointCount W a : ℝ) ^ 2 := by
          exact_mod_cast hedge
        rw [hγj] at hE
        change Real.exp (γ * f j / 2) * _ ≤ _ at hE
        nlinarith
      refine ⟨windowProjection W a, hP, by rwa [hc], hlow, ?_, ?_⟩
      · simpa only [W, hDj, B, f] using hpack
      · simpa only [hγj, f] using hcount
    choose P hP hn hlow hpack hcount using hsets
    let n : ℕ → ℕ := fun j => Nat.card (P j)
    -- The endpoint-pair bound forces these positive cardinalities to infinity.
    have hf : Filter.Tendsto (fun j => (f j : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hdegree
    have hexp : Filter.Tendsto (fun j => Real.exp (γ * f j / 2))
        Filter.atTop Filter.atTop := by
      apply Real.tendsto_exp_atTop.comp
      simpa only [mul_div_assoc, div_mul_eq_mul_div] using
        hf.const_mul_atTop (show 0 < γ / 2 by dsimp [γ]; linarith)
    have hnlim : Filter.Tendsto (fun j => (n j : ℝ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono hlow hexp
    -- Convert the packing bound to a power bound with fixed positive exponent.
    let δ := γ / (4 * B)
    have hδ : 0 < δ := div_pos hγ (mul_pos (by norm_num) hB)
    have hpower : ∀ j, (1 / 2 : ℝ) * (n j : ℝ) ^ (1 + 2 * δ) ≤
        (unitDistanceCount (P j) : ℝ) := by
      intro j
      have hnj : (0 : ℝ) < n j := by exact_mod_cast hn j
      have hlog : Real.log (n j) ≤ B * f j :=
        (Real.log_le_iff_le_exp hnj).mpr (hpack j)
      have hcoeff : 2 * δ = γ / (2 * B) := by dsimp [δ]; ring
      have he : Real.log (n j) * (2 * δ) ≤ γ * f j / 2 := by
        rw [hcoeff]
        calc
          _ ≤ (B * f j) * (γ / (2 * B)) :=
            mul_le_mul_of_nonneg_right hlog (by positivity)
          _ = _ := by field_simp
      have hp : (n j : ℝ) ^ (2 * δ) ≤ Real.exp (γ * f j / 2) := by
        rw [Real.rpow_def_of_pos hnj]
        exact Real.exp_le_exp.mpr he
      have hp' : (n j : ℝ) ^ (1 + 2 * δ) ≤
          (n j : ℝ) * Real.exp (γ * f j / 2) := by
        rw [Real.rpow_add hnj, Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hp hnj.le
      calc
        _ ≤ (1 / 2 : ℝ) * ((n j : ℝ) * Real.exp (γ * f j / 2)) :=
          mul_le_mul_of_nonneg_left hp' (by norm_num)
        _ ≤ _ := by nlinarith [hcount j]
    -- Eventually n^δ ≥ 2, absorbing the factor one half in the paper's bound.
    have hlarge : ∀ᶠ j in Filter.atTop, (2 : ℝ) ≤ (n j : ℝ) ^ δ :=
      ((tendsto_rpow_atTop hδ).comp hnlim).eventually_ge_atTop 2
    have hgood : ∀ᶠ j in Filter.atTop,
        (n j : ℝ) ^ (1 + δ) ≤ (unitDistanceMaximum (n j) : ℝ) := by
      filter_upwards [hlarge] with j hj
      have hnj : (0 : ℝ) < n j := by exact_mod_cast hn j
      have heq : (n j : ℝ) ^ (1 + 2 * δ) =
          (n j : ℝ) ^ (1 + δ) * (n j : ℝ) ^ δ := by
        rw [← Real.rpow_add hnj]
        congr 1
        ring
      have hp := hpower j
      rw [heq] at hp
      have hmul := mul_le_mul_of_nonneg_left hj
        (Real.rpow_nonneg hnj.le (1 + δ))
      have hmax : (unitDistanceCount (P j) : ℝ) ≤ (unitDistanceMaximum (n j) : ℝ) := by
        exact_mod_cast count_le_maximum (P j) (hP j)
      nlinarith
    refine ⟨δ, hδ, Set.infinite_of_not_bddAbove ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨j, hj, hjM⟩ := (hgood.and (hnlim.eventually_gt_atTop (M : ℝ))).exists
    have hmem : n j ∈ {m : ℕ | 0 < m ∧
        (m : ℝ) ^ (1 + δ) ≤ (unitDistanceMaximum m : ℝ)} := ⟨hn j, hj⟩
    have := hM hmem
    exact (not_lt_of_ge (show (n j : ℝ) ≤ M by exact_mod_cast this)) hjM)
  -- HumanLean:proof_end
)
end UnitDistance
