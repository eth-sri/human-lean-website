import Formalization.Result.helpers.Proposition_Ap13.Machinery
import Formalization.Axioms

noncomputable section
namespace UnitDistance

/-- Proposition A.13: a constant uniform in field, degree and signature. -/
theorem paper_A_13 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ) ≤ max 2 (rootDiscriminant K) ^ (C * Module.finrank ℚ K) ∧
      (2 ≤ rootDiscriminant K → (classNumber K : ℝ) ≤ (absoluteDiscriminant K : ℝ) ^ C) := (by
  -- HumanLean:proof_begin
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro K _ _
  let n := Module.finrank ℚ K
  let A := max 2 (rootDiscriminant K)
  let X := Real.exp ((n : ℝ) * (1 + Real.log A / 2))
  let L := (n : ℝ) * (1 + Real.log A / 2) + n * Real.log 2
  have hn : 0 < n := Module.finrank_pos
  have hA : 2 ≤ A := le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hL : 0 ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
    positivity
  -- Minkowski supplies a representative in each class at the enlarged cutoff.
  have hrep := Formalization.Result.helpers.Proposition_Ap13.Machinery.minkowski_representative_cutoff
    K A hApos (le_max_right _ _)
  have hclass := Formalization.Result.helpers.Proposition_Ap13.Machinery.class_number_le_representative_count
    K X hrep
  -- Prime ideal factorization injects ideals into positive n-tuples of the same norm.
  have hideals : Nat.card {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) //
      ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X} ≤
      Nat.card {a : Fin n → ℕ // (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X} := by
    obtain ⟨enc, henc, hpos, hnorm⟩ :=
      Formalization.Result.helpers.Proposition_Ap13.Machinery.ideal_tuple_encoding K
    letI := Formalization.Result.helpers.Proposition_Ap13.Machinery.finite_positive_tuples_below_cutoff n X
    let g : {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) //
        ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X} →
        {a : Fin n → ℕ // (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X} :=
      fun I => ⟨enc I.val, hpos I.val, by rw [hnorm]; exact I.property⟩
    apply Nat.card_le_card_of_injective g
    intro I J h
    exact Subtype.ext (henc (congrArg Subtype.val h))
  -- The disjoint unit boxes fit in the enlarged product region.
  have hboxes := Formalization.Result.helpers.Proposition_Ap13.Machinery.tuple_count_le_product_region_volume n X
  -- Slicing and logarithmic integration give the factorial volume bound.
  have hvolume : MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ 2 ^ n * X} ≤
      ENNReal.ofReal (Real.exp L * L ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
    have hX : 1 ≤ X := by
      apply Real.one_le_exp_iff.mpr
      have hlog : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
      positivity
    have hT : 1 ≤ (2 : ℝ) ^ n * X := by
      have htwo : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    have hlog : Real.log ((2 : ℝ) ^ n * X) = L := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      dsimp [X, L]
      rw [Real.log_exp]
      ring
    have hexp : Real.exp L = (2 : ℝ) ^ n * X := by
      rw [← hlog, Real.exp_log (by positivity)]
    have hv := Formalization.Result.helpers.Proposition_Ap13.Machinery.product_region_volume_bound
      (n - 1) ((2 : ℝ) ^ n * X) hT
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at hv
    simpa only [hlog, ← hexp, Real.log_exp] using hv
  have hcount : (classNumber K : ENNReal) ≤
      ENNReal.ofReal (Real.exp L * L ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
    exact le_trans (by exact_mod_cast hclass.trans hideals) (hboxes.trans hvolume)
  have hreal : (classNumber K : ℝ) ≤
      Real.exp L * L ^ (n - 1) / ((n - 1).factorial : ℝ) := by
    have hb : 0 ≤ Real.exp L * L ^ (n - 1) / ((n - 1).factorial : ℝ) := by positivity
    simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hb] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcount
  -- Absorb the factorial expression into one absolute exponent.
  have hbound : (classNumber K : ℝ) ≤ A ^ ((8 : ℝ) * n) :=
    hreal.trans ((Formalization.Result.helpers.Proposition_Ap13.Machinery.factorial_term_le_exponential L hL n).trans
      (Formalization.Result.helpers.Proposition_Ap13.Machinery.exponential_cutoff_bound n A hA))
  refine ⟨hbound, ?_⟩
  intro hroot
  simpa only [A, n, Formalization.Result.helpers.Proposition_Ap13.Machinery.max_root_rpow_eq_discriminant K hroot] using hbound
  -- HumanLean:proof_end
)
end UnitDistance
