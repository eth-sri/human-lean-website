import Formalization.Axioms
import Formalization.Definition
import Mathlib

namespace Formalization.Result.helpers.Proposition_Ap13.Machinery



theorem discriminant_pos (K : Type) [Field K] [NumberField K] :
    0 < (UnitDistance.absoluteDiscriminant K : ℝ) := by
  exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)

theorem root_discriminant_pos (K : Type) [Field K] [NumberField K] :
    0 < UnitDistance.rootDiscriminant K := by
  exact Real.rpow_pos_of_pos (discriminant_pos K) _

theorem root_discriminant_rpow_degree (K : Type) [Field K] [NumberField K] :
    UnitDistance.rootDiscriminant K ^ (Module.finrank ℚ K : ℝ) =
      (UnitDistance.absoluteDiscriminant K : ℝ) := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  rw [UnitDistance.rootDiscriminant, ← Real.rpow_mul (le_of_lt (discriminant_pos K)),
    inv_mul_cancel₀ hn, Real.rpow_one]

theorem root_discriminant_pow_degree (K : Type) [Field K] [NumberField K] :
    UnitDistance.rootDiscriminant K ^ Module.finrank ℚ K =
      (UnitDistance.absoluteDiscriminant K : ℝ) := by
  rw [← Real.rpow_natCast, root_discriminant_rpow_degree]

theorem max_root_rpow_eq_discriminant (K : Type) [Field K] [NumberField K]
    (hK : 2 ≤ UnitDistance.rootDiscriminant K) (C : ℝ) :
    max 2 (UnitDistance.rootDiscriminant K) ^ (C * Module.finrank ℚ K) =
      (UnitDistance.absoluteDiscriminant K : ℝ) ^ C := by
  rw [max_eq_right hK, mul_comm C, Real.rpow_mul (le_of_lt (root_discriminant_pos K)),
    root_discriminant_rpow_degree]

theorem factorial_ratio_le_one (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_one (pow_pos hn' n)).mpr
  exact_mod_cast Nat.factorial_le_pow n

theorem signature_factor_le_exp_degree (K : Type) [Field K] [NumberField K] :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      Real.exp (Module.finrank ℚ K : ℝ) := by
  have hplaces : NumberField.InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hbase : 4 / Real.pi ≤ Real.exp 1 := by
    have hp := Real.pi_gt_three
    have he := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    have : 4 / Real.pi ≤ 2 := (div_le_iff₀ Real.pi_pos).mpr (by linarith)
    linarith
  calc
    _ ≤ (Real.exp 1) ^ NumberField.InfinitePlace.nrComplexPlaces K :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ (Real.exp 1) ^ Module.finrank ℚ K :=
      pow_le_pow_right₀ (by simpa using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hplaces
    _ = _ := Real.exp_one_pow _

theorem sqrt_discriminant_le_exp (K : Type) [Field K] [NumberField K]
    (A : ℝ) (hA : 0 < A) (hroot : UnitDistance.rootDiscriminant K ≤ A) :
    Real.sqrt (UnitDistance.absoluteDiscriminant K : ℝ) ≤
      Real.exp ((Module.finrank ℚ K : ℝ) * Real.log A / 2) := by
  calc
    _ = Real.sqrt (UnitDistance.rootDiscriminant K ^ Module.finrank ℚ K) := by
      rw [root_discriminant_pow_degree]
    _ ≤ Real.sqrt (A ^ Module.finrank ℚ K) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ (le_of_lt (root_discriminant_pos K)) hroot _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hA),
        Real.rpow_def_of_pos hA]
      congr 1
      ring

theorem minkowski_representative_cutoff (K : Type) [Field K] [NumberField K]
    (A : ℝ) (hA : 0 < A) (hroot : UnitDistance.rootDiscriminant K ≤ A)
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
      ClassGroup.mk0 I = c ∧
        ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤
          Real.exp ((Module.finrank ℚ K : ℝ) * (1 + Real.log A / 2)) := by
  obtain ⟨I, hc, hI⟩ := UnitDistance.minkowskiIdealClassBound K c
  refine ⟨I, hc, hI.trans ?_⟩
  have hfac := factorial_ratio_le_one (Module.finrank ℚ K) Module.finrank_pos
  have hsig := signature_factor_le_exp_degree K
  have hsqrt := sqrt_discriminant_le_exp K A hA hroot
  calc
    _ ≤ Real.exp (Module.finrank ℚ K : ℝ) *
        Real.sqrt (UnitDistance.absoluteDiscriminant K : ℝ) := by
      gcongr
      calc
        _ ≤ (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K * 1 := by
          gcongr
        _ ≤ _ := by simpa using hsig
    _ ≤ Real.exp (Module.finrank ℚ K : ℝ) *
        Real.exp ((Module.finrank ℚ K : ℝ) * Real.log A / 2) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem cutoff_log_ge_degree (n : ℕ) (A : ℝ) (hA : 2 ≤ A) :
    (n : ℝ) ≤ Real.log (Real.exp ((n : ℝ) * (1 + Real.log A / 2))) := by
  rw [Real.log_exp]
  have hlog : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

theorem finite_ideals_below_real_cutoff (K : Type) [Field K] [NumberField K] (X : ℝ) :
    Finite {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) //
      ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X} := by
  apply Set.Finite.to_subtype
  apply (Ideal.finite_setOf_absNorm_le₀ (S := NumberField.RingOfIntegers K) ⌊X⌋₊).subset
  intro I hI
  exact Nat.le_floor hI

theorem class_number_le_representative_count (K : Type) [Field K] [NumberField K]
    (X : ℝ)
    (hrep : ∀ c : ClassGroup (NumberField.RingOfIntegers K),
      ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
        ClassGroup.mk0 I = c ∧ ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X) :
    UnitDistance.classNumber K ≤
      Nat.card {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) //
        ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X} := by
  letI := finite_ideals_below_real_cutoff K X
  have hsurj : Function.Surjective
      (fun I : {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) //
        ((I : Ideal (NumberField.RingOfIntegers K)).absNorm : ℝ) ≤ X} =>
        ClassGroup.mk0 I.val) := by
    intro c
    obtain ⟨I, hc, hI⟩ := hrep c
    exact ⟨⟨I, hI⟩, hc⟩
  simpa [UnitDistance.classNumber, NumberField.classNumber, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_surjective _ hsurj

theorem positive_tuple_coordinate_le_product {n : ℕ} (a : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (i : Fin n) : a i ≤ ∏ j, a j := by
  exact Finset.single_le_prod' (fun j _ => ha j) (Finset.mem_univ i)

theorem finite_positive_tuples_below_cutoff (n : ℕ) (X : ℝ) :
    Finite {a : Fin n → ℕ // (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X} := by
  apply Set.Finite.to_subtype
  apply (Set.Finite.pi (fun _ : Fin n => Set.finite_Iic ⌊X⌋₊)).subset
  intro a ha i _
  apply Nat.le_floor
  exact le_trans (by exact_mod_cast positive_tuple_coordinate_le_product a ha.1 i) ha.2

theorem tuple_box_subset_product_region {n : ℕ} {a : Fin n → ℕ} {X : ℝ}
    (ha : ∀ i, 0 < a i) (hprod : ((∏ i, a i : ℕ) : ℝ) ≤ X) :
    Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) ⊆
      {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ 2 ^ n * X} := by
  intro x hx
  have hi (i : Fin n) : (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1 := hx i (Set.mem_univ i)
  have hone (i : Fin n) : (1 : ℝ) ≤ a i := by exact_mod_cast ha i
  refine ⟨fun i => (hone i).trans (hi i).1, ?_⟩
  calc
    ∏ i, x i ≤ ∏ i, 2 * (a i : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _; linarith [(hi i).1, hone i]
      · intro i _; linarith [(hi i).2, hone i]
    _ = 2 ^ n * ((∏ i, a i : ℕ) : ℝ) := by simp [Finset.prod_mul_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

theorem tuple_boxes_disjoint {n : ℕ} {a b : Fin n → ℕ} (hab : a ≠ b) :
    Disjoint (Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)))
      (Set.pi Set.univ (fun i => Set.Ico (b i : ℝ) ((b i : ℝ) + 1))) := by
  rw [Set.disjoint_left]
  intro x ha hb
  apply hab
  funext i
  have ha' := ha i (Set.mem_univ i)
  have hb' := hb i (Set.mem_univ i)
  have hab' : (a i : ℝ) < (b i : ℝ) + 1 := ha'.1.trans_lt hb'.2
  have hba' : (b i : ℝ) < (a i : ℝ) + 1 := hb'.1.trans_lt ha'.2
  have hab'' : a i < b i + 1 := by exact_mod_cast hab'
  have hba'' : b i < a i + 1 := by exact_mod_cast hba'
  omega

theorem tuple_box_volume {n : ℕ} (a : Fin n → ℕ) :
    MeasureTheory.volume (Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1))) = 1 := by
  rw [Real.volume_pi_Ico]
  simp

theorem finite_tuple_count_le_product_region_volume {n : ℕ} (S : Finset (Fin n → ℕ))
    (X : ℝ) (hS : ∀ a ∈ S, (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X) :
    (S.card : ENNReal) ≤ MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ 2 ^ n * X} := by
  classical
  calc
    (S.card : ENNReal) = MeasureTheory.volume
        (⋃ a ∈ S, Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1))) := by
      rw [MeasureTheory.measure_biUnion_finset]
      · simp [tuple_box_volume]
      · intro a _ b _ hab; exact tuple_boxes_disjoint hab
      · intro a _; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
    _ ≤ _ := MeasureTheory.measure_mono (by
      intro x hx
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp hx
      exact tuple_box_subset_product_region (hS a ha).1 (hS a ha).2 hx)

theorem factorial_term_le_exponential (L : ℝ) (hL : 0 ≤ L) (n : ℕ) :
    Real.exp L * L ^ (n - 1) / ((n - 1).factorial : ℝ) ≤ Real.exp (2 * L) := by
  calc
    _ = Real.exp L * (L ^ (n - 1) / ((n - 1).factorial : ℝ)) := by ring
    _ ≤ Real.exp L * Real.exp L :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp L hL _) (le_of_lt (Real.exp_pos _))
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exponential_cutoff_bound (n : ℕ) (A : ℝ) (hA : 2 ≤ A) :
    Real.exp (2 * ((n : ℝ) * (1 + Real.log A / 2) + n * Real.log 2)) ≤
      A ^ ((8 : ℝ) * n) := by
  have hApos : 0 < A := by linarith
  have hlog : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hA
  have htwo := Real.log_two_gt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Real.rpow_def_of_pos hApos]
  apply Real.exp_le_exp.mpr
  have h : 2 * (1 + Real.log A / 2 + Real.log 2) ≤ 8 * Real.log A := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h hn]

theorem tuple_count_le_product_region_volume (n : ℕ) (X : ℝ) :
    (Nat.card {a : Fin n → ℕ // (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X} : ENNReal) ≤
      MeasureTheory.volume {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ 2 ^ n * X} := by
  classical
  let S : Set (Fin n → ℕ) := {a | (∀ i, 0 < a i) ∧ ((∏ i, a i : ℕ) : ℝ) ≤ X}
  letI : Finite S := finite_positive_tuples_below_cutoff n X
  have hS := Set.toFinite S
  have h := finite_tuple_count_le_product_region_volume hS.toFinset X (by
    intro a ha
    exact hS.mem_toFinset.mp ha)
  rwa [← Set.ncard_eq_toFinset_card S hS, Set.ncard_def] at h

theorem log_power_integral (T : ℝ) (hT : 1 ≤ T) (n : ℕ) :
    ∫ y in (1 : ℝ)..T, (Real.log T - Real.log y) ^ n / y =
      Real.log T ^ (n + 1) / (n + 1 : ℝ) := by
  have hypos (y : ℝ) (hy : y ∈ Set.uIcc 1 T) : 0 < y := by
    rw [Set.uIcc_of_le hT] at hy
    linarith [hy.1]
  have hderiv (y : ℝ) (hy : y ∈ Set.uIcc 1 T) :
      HasDerivAt (fun y : ℝ => -(Real.log T - Real.log y) ^ (n + 1) / (n + 1 : ℝ))
        ((Real.log T - Real.log y) ^ n / y) y := by
    have h := ((((Real.hasDerivAt_log (ne_of_gt (hypos y hy))).const_sub (Real.log T)).pow
      (n + 1)).neg).div_const (n + 1 : ℝ)
    convert h using 1 <;> simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] <;>
      field_simp <;> ring
  have hcont : ContinuousOn (fun y : ℝ => (Real.log T - Real.log y) ^ n / y)
      (Set.uIcc 1 T) := by
    apply ContinuousOn.div
    · exact (continuousOn_const.sub (Real.continuousOn_log.mono (fun y hy =>
        ne_of_gt (hypos y hy)))).pow n
    · exact continuousOn_id
    · intro y hy; exact ne_of_gt (hypos y hy)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  simpa [neg_div] using h

theorem product_slice_integral (T : ℝ) (hT : 1 ≤ T) (n : ℕ) :
    ∫ y in (1 : ℝ)..T, (T / y) * (Real.log (T / y)) ^ n / (n.factorial : ℝ) =
      T * Real.log T ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  calc
    _ = ∫ y in (1 : ℝ)..T,
        (T / (n.factorial : ℝ)) * ((Real.log T - Real.log y) ^ n / y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hypos : 0 < y := by rw [Set.uIcc_of_le hT] at hy; linarith [hy.1]
      dsimp
      rw [Real.log_div hTpos.ne' hypos.ne']
      ring
    _ = (T / (n.factorial : ℝ)) * (Real.log T ^ (n + 1) / (n + 1 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, log_power_integral T hT n]
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_mul_eq_div_mul_one_div]
      ring

theorem measurable_product_region (n : ℕ) (T : ℝ) :
    MeasurableSet {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T} := by
  have hprod : Continuous (fun x : Fin n → ℝ => ∏ i, x i) := by fun_prop
  have hcoords : MeasurableSet {x : Fin n → ℝ | ∀ i, 1 ≤ x i} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  exact hcoords.inter (measurableSet_le hprod.measurable measurable_const)

theorem product_region_cons_iff (n : ℕ) (T y : ℝ) (x : Fin n → ℝ) :
    ((∀ i, 1 ≤ (Fin.cons y x : Fin (n + 1) → ℝ) i) ∧
      ∏ i, (Fin.cons y x : Fin (n + 1) → ℝ) i ≤ T) ↔
      y ∈ Set.Icc 1 T ∧ (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T / y := by
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
  constructor
  · rintro ⟨⟨hy, hx⟩, hprod⟩
    have hypos : 0 < y := by linarith
    have hp : 1 ≤ ∏ i, x i := Finset.one_le_prod (fun i _ => hx i)
    refine ⟨⟨hy, ?_⟩, hx, (le_div_iff₀ hypos).mpr (by simpa [mul_comm] using hprod)⟩
    nlinarith
  · rintro ⟨⟨hy, _⟩, hx, hprod⟩
    have hypos : 0 < y := by linarith
    exact ⟨⟨hy, hx⟩, by simpa [mul_comm] using (le_div_iff₀ hypos).mp hprod⟩

theorem product_region_slice_measure (n : ℕ) (T : ℝ) :
    MeasureTheory.volume {x : Fin (n + 1) → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T} =
      ∫⁻ y in Set.Icc 1 T, MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T / y} := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he := (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  let S : Set (Fin (n + 1) → ℝ) := {x | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T}
  have hS : MeasurableSet S := measurable_product_region _ _
  have hpre : e.symm ⁻¹' S =
      {p : ℝ × (Fin n → ℝ) | p.1 ∈ Set.Icc 1 T ∧ (∀ i, 1 ≤ p.2 i) ∧ ∏ i, p.2 i ≤ T / p.1} := by
    ext p
    change ((∀ i, 1 ≤ e.symm p i) ∧ ∏ i, e.symm p i ≤ T) ↔ _
    have heq : e.symm p = Fin.cons p.1 p.2 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
    rw [heq]
    exact product_region_cons_iff _ _ _ _
  calc
    _ = MeasureTheory.volume (e.symm ⁻¹' S) := (he.measure_preimage hS.nullMeasurableSet).symm
    _ = ∫⁻ y, MeasureTheory.volume {x : Fin n → ℝ |
        y ∈ Set.Icc 1 T ∧ (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T / y} := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply (e.symm.measurable hS)]
      simp only [hpre, Set.preimage_setOf_eq]
    _ = _ := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Icc 1 T <;> simp [hy]

theorem product_region_one_volume (T : ℝ) :
    MeasureTheory.volume {x : Fin 1 → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T} ≤
      ENNReal.ofReal T := by
  calc
    _ ≤ MeasureTheory.volume (Set.Icc (fun _ : Fin 1 => (1 : ℝ)) (fun _ => T)) := by
      apply MeasureTheory.measure_mono
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro i
      fin_cases i
      simpa using hx.2
    _ = ENNReal.ofReal (T - 1) := by rw [Real.volume_Icc_pi]; simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

theorem product_region_volume_bound (n : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    MeasureTheory.volume {x : Fin (n + 1) → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T} ≤
      ENNReal.ofReal (T * Real.log T ^ n / (n.factorial : ℝ)) := by
  induction n generalizing T with
  | zero => simpa using product_region_one_volume T
  | succ n ih =>
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hypos (y : ℝ) (hy : y ∈ Set.Icc 1 T) : 0 < y := by linarith [hy.1]
    have hdiv (y : ℝ) (hy : y ∈ Set.Icc 1 T) : 1 ≤ T / y :=
      (le_div_iff₀ (hypos y hy)).mpr (by simpa using hy.2)
    let f := fun y : ℝ => (T / y) * Real.log (T / y) ^ n / (n.factorial : ℝ)
    have hf : ContinuousOn f (Set.Icc 1 T) := by
      have hd : ContinuousOn (fun y : ℝ => T / y) (Set.Icc 1 T) :=
        continuousOn_const.div continuousOn_id (fun y hy => (hypos y hy).ne')
      exact (hd.mul ((hd.log (fun y hy => (div_pos hTpos (hypos y hy)).ne')).pow n)).div_const _
    have hfnonneg (y : ℝ) (hy : y ∈ Set.Icc 1 T) : 0 ≤ f y := by
      have hlog := Real.log_nonneg (hdiv y hy)
      have hy' := hypos y hy
      dsimp [f]
      positivity
    calc
      _ = ∫⁻ y in Set.Icc 1 T, MeasureTheory.volume
          {x : Fin (n + 1) → ℝ | (∀ i, 1 ≤ x i) ∧ ∏ i, x i ≤ T / y} :=
        product_region_slice_measure _ _
      _ ≤ ∫⁻ y in Set.Icc 1 T, ENNReal.ofReal (f y) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro y hy
        exact ih (T / y) (hdiv y hy)
      _ = ENNReal.ofReal (∫ y in Set.Icc 1 T, f y) := by
        symm
        apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        · exact hf.integrableOn_Icc
        · exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall hfnonneg)
      _ = ENNReal.ofReal (∫ y in (1 : ℝ)..T, f y) := by
        rw [intervalIntegral.integral_of_le hT, MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = _ := by rw [product_slice_integral T hT n]

theorem prime_power_tuple_encoding {α : Type*} {n : ℕ}
    (p f : α → ℕ) (slot : α → Fin n)
    (hp : ∀ a, (p a).Prime) (hf : ∀ a, 0 < f a)
    (hslot : Function.Injective (fun a => (p a, slot a))) :
    ∃ enc : Multiset α → (Fin n → ℕ), Function.Injective enc ∧
      (∀ s i, 0 < enc s i) ∧
      (∀ s, ∏ i, enc s i = (s.map (fun a => p a ^ f a)).prod) := by
  classical
  let enc := fun (s : Multiset α) (i : Fin n) =>
    ((s.filter (fun a => slot a = i)).map (fun a => p a ^ f a)).prod
  have hpos (s : Multiset α) (i : Fin n) : 0 < enc s i := by
    apply Multiset.prod_pos
    intro v hv
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hv
    exact pow_pos (hp a).pos _
  have hcons (a : α) (s : Multiset α) (i : Fin n) :
      enc (a ::ₘ s) i = (if slot a = i then p a ^ f a else 1) * enc s i := by
    dsimp [enc]
    by_cases h : slot a = i <;> simp [h]
  have hfactor (s : Multiset α) (a : α) :
      (enc s (slot a)).factorization (p a) = f a * s.count a := by
    induction s using Multiset.induction_on with
    | empty => simp [enc]
    | cons b s ih =>
      rw [hcons]
      by_cases hba : b = a
      · subst b
        simp only [ite_true]
        rw [Nat.factorization_mul (pow_ne_zero _ (hp a).ne_zero) (hpos s _).ne',
          Finsupp.add_apply, Nat.factorization_pow_self (hp a), ih]
        simp [Multiset.count_cons, Nat.mul_add, Nat.add_comm]
      · have hcount : (b ::ₘ s).count a = s.count a := by simp [hba, Ne.symm hba]
        rw [hcount]
        by_cases hs : slot b = slot a
        · have hprime : p b ≠ p a := by
            intro h
            exact hba (hslot (Prod.ext h hs))
          rw [if_pos hs, Nat.factorization_mul (pow_ne_zero _ (hp b).ne_zero) (hpos s _).ne',
            Finsupp.add_apply, (hp b).factorization_pow, Finsupp.single_apply,
            if_neg hprime, zero_add, ih]
        · rw [if_neg hs, one_mul, ih]
  have hinj : Function.Injective enc := by
    intro s t hst
    apply Multiset.ext.mpr
    intro a
    have h := congrArg (fun q : Fin n → ℕ => (q (slot a)).factorization (p a)) hst
    dsimp only at h
    rw [hfactor, hfactor] at h
    exact Nat.eq_of_mul_eq_mul_left (hf a) h
  refine ⟨enc, hinj, hpos, ?_⟩
  intro s
  induction s using Multiset.induction_on with
  | empty => simp [enc]
  | cons a s ih =>
    simp_rw [hcons]
    rw [Finset.prod_mul_distrib, ih]
    simp

theorem prime_ideal_tuple_slots (K : Type) [Field K] [NumberField K] :
    ∃ slot : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥} →
        Fin (Module.finrank ℚ K),
      Function.Injective (fun P => ((Ideal.under ℤ P.val).absNorm, slot P)) := by
  classical
  let n := Module.finrank ℚ K
  have hn : 0 < n := Module.finrank_pos
  have hlabel (p : ℕ) (hp : p.Prime) :
      ∃ l : Ideal (NumberField.RingOfIntegers K) → Fin n,
        Set.InjOn l (primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K)) := by
    letI : Fact p.Prime := ⟨hp⟩
    let S := primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K)
    have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
    have hcard : S.card ≤ n :=
      Ideal.card_primesOverFinset_le_finrank (NumberField.RingOfIntegers K) ℚ K hbot
    obtain ⟨e⟩ : Nonempty (S ↪ Fin n) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    refine ⟨fun P => if h : P ∈ S then e ⟨P, h⟩ else ⟨0, hn⟩, ?_⟩
    intro P hP Q hQ h
    change P ∈ S at hP
    change Q ∈ S at hQ
    dsimp only at h
    rw [dif_pos hP, dif_pos hQ] at h
    exact congrArg Subtype.val (e.injective h)
  let label := fun p (hp : p.Prime) => (hlabel p hp).choose
  have hinj (p : ℕ) (hp : p.Prime) : Set.InjOn (label p hp)
      (primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K)) :=
    (hlabel p hp).choose_spec
  let p := fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥} =>
    (Ideal.under ℤ P.val).absNorm
  have hp (P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥}) :
      (p P).Prime := by
    letI : P.val.IsPrime := P.property.1
    letI : NeZero P.val := ⟨P.property.2⟩
    exact Nat.absNorm_under_prime P.val
  have hmem (P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥}) :
      P.val ∈ primesOverFinset (Ideal.span {((p P : ℕ) : ℤ)})
        (NumberField.RingOfIntegers K) := by
    letI : Fact (p P).Prime := ⟨hp P⟩
    apply (mem_primesOverFinset_iff (by simpa using (hp P).ne_zero) _).mpr
    exact ⟨P.property.1, Int.liesOver_span_absNorm P.val⟩
  refine ⟨fun P => label (p P) (hp P) P.val, ?_⟩
  intro P Q h
  have hprime : p P = p Q := congrArg Prod.fst h
  have hslot : label (p P) (hp P) P.val = label (p Q) (hp Q) Q.val := congrArg Prod.snd h
  apply Subtype.ext
  apply hinj (p Q) (hp Q) ?_ (hmem Q)
  · simpa only [hprime] using hslot
  · simpa only [hprime] using hmem P

theorem nonzero_ideal_prime_multiset (K : Type) [Field K] [NumberField K] :
    ∃ fac : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) →
        Multiset {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥},
      Function.Injective fac ∧
      ∀ I, ((fac I).map Subtype.val).prod = (I : Ideal (NumberField.RingOfIntegers K)) := by
  classical
  have hprime (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)))
      (P : Ideal (NumberField.RingOfIntegers K))
      (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) :
      P.IsPrime ∧ P ≠ ⊥ := by
    have h := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact ⟨Ideal.isPrime_of_prime h, h.ne_zero⟩
  let fac := fun I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) =>
    (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).attach.map
      (fun P => (⟨P.val, hprime I P.val P.property⟩ :
        {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥}))
  have hprod (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))) :
      ((fac I).map Subtype.val).prod = (I : Ideal (NumberField.RingOfIntegers K)) := by
    dsimp [fac]
    rw [Multiset.map_map]
    change ((UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers K))).attach.map Subtype.val).prod = _
    rw [Multiset.attach_map_val]
    exact prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)
  refine ⟨fac, ?_, hprod⟩
  intro I J h
  apply Subtype.ext
  rw [← hprod I, ← hprod J, h]

theorem prime_ideal_norm_data (K : Type) [Field K] [NumberField K]
    (P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥}) :
    let p := (Ideal.under ℤ P.val).absNorm
    let f := (Ideal.span {(p : ℤ)}).inertiaDeg P.val
    p.Prime ∧ 0 < f ∧ P.val.absNorm = p ^ f := by
  dsimp only
  letI : P.val.IsPrime := P.property.1
  letI : NeZero P.val := ⟨P.property.2⟩
  have hp := Nat.absNorm_under_prime P.val
  letI : Fact (Ideal.under ℤ P.val).absNorm.Prime := ⟨hp⟩
  refine ⟨hp, ?_, Ideal.absNorm_eq_pow_inertiaDeg' P.val hp⟩
  exact Nat.pos_of_ne_zero (Ideal.inertiaDeg_ne_zero _ _)

theorem ideal_tuple_encoding (K : Type) [Field K] [NumberField K] :
    ∃ enc : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) →
        (Fin (Module.finrank ℚ K) → ℕ),
      Function.Injective enc ∧ (∀ I i, 0 < enc I i) ∧
      ∀ I, ∏ i, enc I i = (I : Ideal (NumberField.RingOfIntegers K)).absNorm := by
  classical
  let P := {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥}
  let p : P → ℕ := fun P => (Ideal.under ℤ P.val).absNorm
  let f : P → ℕ := fun P => (Ideal.span {((p P : ℕ) : ℤ)}).inertiaDeg P.val
  obtain ⟨slot, hslot⟩ := prime_ideal_tuple_slots K
  obtain ⟨enc, henc, hpos, hprod⟩ := prime_power_tuple_encoding p f slot
    (fun P => (prime_ideal_norm_data K P).1) (fun P => (prime_ideal_norm_data K P).2.1) hslot
  obtain ⟨fac, hfac, hfacprod⟩ := nonzero_ideal_prime_multiset K
  refine ⟨enc ∘ fac, henc.comp hfac, fun I i => hpos (fac I) i, ?_⟩
  intro I
  change ∏ i, enc (fac I) i = _
  rw [hprod]
  calc
    _ = ((fac I).map (fun P => P.val.absNorm)).prod := by
      congr 1
      apply Multiset.map_congr rfl
      intro P _
      exact (prime_ideal_norm_data K P).2.2.symm
    _ = (((fac I).map Subtype.val).prod).absNorm := by
      rw [map_multiset_prod, Multiset.map_map]
      rfl
    _ = _ := by rw [hfacprod]



end Formalization.Result.helpers.Proposition_Ap13.Machinery
