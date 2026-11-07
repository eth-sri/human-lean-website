import Formalization.Result.helpers.Proposition_3p7.Machinery
import Formalization.Definition
import Formalization.Result.Proposition_Ap13

noncomputable section
namespace UnitDistance

/-- Proposition 3.7, the second numbered presentation of the class estimate. -/
theorem paper_3_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ) ≤ max 2 (rootDiscriminant K) ^ (C * Module.finrank ℚ K) ∧
      (2 ≤ rootDiscriminant K → (classNumber K : ℝ) ≤ (absoluteDiscriminant K : ℝ) ^ C) := (by
  -- HumanLean:proof_begin
  -- A.13 proves the same uniform estimate by Minkowski and divisor counting,
  -- including its discriminant form when the root discriminant is at least two.
  exact paper_A_13
  -- HumanLean:proof_end
)
end UnitDistance
