import Formalization.Result.helpers.Theorem_1p1.Machinery
import Formalization.Definition
import Formalization.Result.Theorem_2p3
import Formalization.Result.Proposition_3p8

noncomputable section
namespace UnitDistance

/-- Theorem 1.1, for infinitely many positive integer sizes. -/
theorem paper_1_1 :
    ∃ δ : ℝ, 0 < δ ∧ Set.Infinite {n : ℕ |
      0 < n ∧ (n : ℝ) ^ (1 + δ) ≤ (unitDistanceMaximum n : ℝ)} := (by
  -- HumanLean:proof_begin
  -- Fix a sufficiently large ell before varying the tower level.
  obtain ⟨C_F, C_H, _, _, ell₀, _, htower⟩ := paper_3_8
  obtain ⟨A, H, hH, _, hprimes, _, _, _, _, _, _, hdegree, _, hclass, _, hγ⟩ :=
    htower ell₀ le_rfl
  -- The tower supplies admissibility, fixed primes, and a uniform class bound.
  -- Theorem 2.3 already passes from the planar sets to infinitely many sizes.
  exact paper_2_3 A hprimes hdegree H hH (fun j => (hclass j).2) hγ
  -- HumanLean:proof_end
)
end UnitDistance
