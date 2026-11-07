import Formalization.Axioms
import Formalization.Definition
import Formalization.Result.Proposition_2p2
import Mathlib

namespace Formalization.Result.helpers.Lemma_2p4.Machinery



lemma overlap_positive {R : ℝ} (hR : 1 / 2 < R) :
    0 < UnitDistance.discOverlapRatio R := by
  have hR0 : 0 < R := by linarith
  have hsub : Metric.ball (1 / 2 : ℂ) (R - 1 / 2) ⊆
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R := by
    intro z hz
    have hz' := Metric.mem_ball.mp hz
    have h0 : dist (1 / 2 : ℂ) 0 = (1 / 2 : ℝ) := by norm_num [dist_eq_norm]
    have h1 : dist (1 / 2 : ℂ) 1 = (1 / 2 : ℝ) := by norm_num [dist_eq_norm]
    constructor
    · exact Metric.mem_closedBall.mpr (by linarith [dist_triangle z (1 / 2 : ℂ) 0])
    · exact Metric.mem_closedBall.mpr (by linarith [dist_triangle z (1 / 2 : ℂ) 1])
  have hp : 0 < MeasureTheory.volume
      (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R) :=
    lt_of_lt_of_le (Metric.measure_ball_pos _ _ (by linarith))
      (MeasureTheory.measure_mono hsub)
  have hf : MeasureTheory.volume
      (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  exact div_pos (ENNReal.toReal_pos hp.ne' hf.ne) (mul_pos Real.pi_pos (sq_pos_of_pos hR0))

lemma exponential_overlap_bound {γ ρ : ℝ} {f n : ℕ}
    (hf : 0 < f) (hρ : 0 < ρ)
    (hlog : -γ / 2 < Real.log ρ) (hn : Real.exp (γ * f) ≤ n) :
    Real.exp (γ * f / 2) < (n : ℝ) * ρ ^ f := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hexp : Real.exp (γ * f / 2) < Real.exp (γ * f) * ρ ^ f := by
    rw [← Real.exp_log hρ, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_right hlog hf']
  exact hexp.trans_le (mul_le_mul_of_nonneg_right hn (pow_nonneg hρ.le _))

lemma select_from_integral_ratio {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (N E : X → ℝ) (k c : ℝ)
    (hN : MeasureTheory.Integrable N μ) (hE : MeasureTheory.Integrable E μ)
    (hN0 : ∀ x, 0 ≤ N x) (hempty : ∀ x, N x = 0 → E x = 0)
    (hmean : 0 < ∫ x, N x ∂μ)
    (hratio : (∫ x, E x ∂μ) = c * ∫ x, N x ∂μ) (hkc : k < c) :
    ∃ x, 0 < N x ∧ k * N x ≤ E x := by
  by_contra h
  have hbound : ∀ x, E x ≤ k * N x := by
    intro x
    by_cases hx : N x = 0
    · simp [hx, hempty x hx]
    · have hxpos := lt_of_le_of_ne (hN0 x) (Ne.symm hx)
      exact (lt_of_not_ge (fun he => h ⟨x, hxpos, he⟩)).le
  have hi := MeasureTheory.integral_mono hE (hN.const_mul k) hbound
  rw [MeasureTheory.integral_const_mul, hratio] at hi
  exact (mul_lt_mul_of_pos_right hkc hmean).not_ge hi

lemma embedding_pairs {A : UnitDistance.AdmissibleDatum} (W : UnitDistance.MinkowskiWindow A) :
    Function.Bijective (fun jb : Fin (Module.finrank ℚ A.L) × Bool =>
      if jb.2 then (starRingEnd ℂ).comp (W.σ jb.1) else W.σ jb.1) := by
  classical
  let τ := fun jb : Fin (Module.finrank ℚ A.L) × Bool =>
    if jb.2 then (starRingEnd ℂ).comp (W.σ jb.1) else W.σ jb.1
  have hrestrict : ∀ j b, (τ (j, b)).comp (algebraMap A.L A.K) =
      (W.σ j).comp (algebraMap A.L A.K) := by
    intro j b
    cases b
    · rfl
    · ext x
      have hx : ((W.σ j) (algebraMap A.L A.K x)).im = 0 :=
        A.realL ((W.σ j).comp (algebraMap A.L A.K)) x
      apply Complex.ext <;> simp [τ, hx]
  have hne : ∀ j, (starRingEnd ℂ).comp (W.σ j) ≠ W.σ j := by
    intro j heq
    have hi := congrArg (fun e : A.K →+* ℂ => e A.i) heq
    have him : (W.σ j A.i).im = 0 := by
      have := congrArg Complex.im hi
      change -(W.σ j A.i).im = (W.σ j A.i).im at this
      linarith
    have hs : (W.σ j A.i) ^ 2 = -1 := by rw [← map_pow, A.i_sq, map_neg, map_one]
    have hsre := congrArg Complex.re hs
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
      Complex.one_re] at hsre
    nlinarith [sq_nonneg (W.σ j A.i).re]
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨j, b⟩ ⟨k, d⟩ h
    have hjk : j = k := W.embeddings.injective (by
      rw [← hrestrict j b, ← hrestrict k d]
      exact congrArg (fun e : A.K →+* ℂ => e.comp (algebraMap A.L A.K)) h)
    subst k
    cases b <;> cases d
    · rfl
    · exact False.elim (hne j h.symm)
    · exact False.elim (hne j h)
    · rfl
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      NumberField.Embeddings.card]
    exact (Nat.mul_comm _ _).trans
      (UnitDistance.idealArithmeticFacts.2 A.L A.K A.realL A.i A.i_sq
        A.generated A.c A.c_ne_one).2.1.symm

lemma denominator_pos (A : UnitDistance.AdmissibleDatum) :
    0 < UnitDistance.admissibleDenominator A := by
  unfold UnitDistance.admissibleDenominator UnitDistance.admissiblePrimeProduct
  exact pow_pos (Finset.prod_pos (fun b _ => (A.q_prime b).pos)) _

lemma window_lattice {A : UnitDistance.AdmissibleDatum} (W : UnitDistance.MinkowskiWindow A) :
    ∃ (Λ : Submodule ℤ (Fin (Module.finrank ℚ A.L) → ℂ))
      (b : Module.Basis (Fin (2 * Module.finrank ℚ A.L)) ℝ
        (Fin (Module.finrank ℚ A.L) → ℂ)),
      (∀ z, z ∈ Λ ↔ ∃ x : A.K,
        IsIntegral ℤ ((UnitDistance.admissibleDenominator A : A.K) * x) ∧
        ∀ j, z j = W.σ j x) ∧
      Λ = Submodule.span ℤ (Set.range b) ∧
      ∃ T : Set (Fin (Module.finrank ℚ A.L) → ℂ),
        MeasurableSet T ∧ Bornology.IsBounded T ∧
        MeasureTheory.IsAddFundamentalDomain Λ T ∧
        0 < MeasureTheory.volume T ∧ MeasureTheory.volume T < ⊤ := by
  classical
  let d : A.K := UnitDistance.admissibleDenominator A
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (denominator_pos A).ne'
  let I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers A.K)) A.K)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton _ d⁻¹)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hd))
  have hI : ∀ x : A.K, x ∈ (I : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers A.K)) A.K) ↔ IsIntegral ℤ (d * x) := by
    intro x
    change x ∈ FractionalIdeal.spanSingleton _ d⁻¹ ↔ _
    rw [FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨z, hz⟩
      have hz' : (z : A.K) * d⁻¹ = x := hz
      have hx : d * x = z := by rw [← hz']; field_simp
      rw [hx]
      exact z.property
    · intro hx
      refine ⟨⟨d * x, hx⟩, ?_⟩
      change (d * x) * d⁻¹ = x
      field_simp
  let Φ : A.K →ₗ[ℤ] (Fin (Module.finrank ℚ A.L) → ℂ) :=
    { toFun := fun x j => W.σ j x
      map_add' := by intro x y; ext j; exact map_add _ _ _
      map_smul' := by intro n x; ext j; exact map_zsmul _ _ _ }
  let Λ := ((I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers A.K)) A.K) :
    Submodule (NumberField.RingOfIntegers A.K) A.K).restrictScalars ℤ |>.map Φ
  have hΛ : (Λ : Set (Fin (Module.finrank ℚ A.L) → ℂ)) =
      {z | ∃ x ∈ (I : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers A.K)) A.K), ∀ j, z j = W.σ j x} := by
    ext z
    change (∃ x, x ∈ (I : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers A.K)) A.K) ∧ Φ x = z) ↔ _
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, fun _ => rfl⟩
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, hx, (funext hz).symm⟩
  obtain ⟨b, hb, T, hT⟩ := UnitDistance.minkowskiFractionalIdealLattice
    A.K _ W.σ (embedding_pairs W) I Λ hΛ
  refine ⟨Λ, b, ?_, hb, T, hT⟩
  intro z
  change z ∈ (Λ : Set _) ↔ _
  rw [hΛ]
  simp only [Set.mem_setOf_eq, hI, d]

lemma real_card_eq_tsum (X : Type*) :
    (Nat.card X : ℝ) = (∑' _ : X, (1 : ENNReal)).toReal := by
  classical
  cases finite_or_infinite X
  · letI := Fintype.ofFinite X
    simp [Nat.card_eq_fintype_card, tsum_fintype]
  · simp [ENNReal.tsum_one, ENat.card_eq_top_of_infinite]

lemma real_count_eq_indicator_sum {X : Type*} (S : Set X) :
    (Nat.card S : ℝ) = (∑' x : X, S.indicator (fun _ => (1 : ENNReal)) x).toReal := by
  classical
  rw [real_card_eq_tsum]
  congr 1
  exact tsum_subtype S (fun _ => (1 : ENNReal))

lemma unfold_window_indicator {f : ℕ} (Λ : Submodule ℤ (Fin f → ℂ)) [Countable Λ]
    {T S : Set (Fin f → ℂ)} (hT : MeasureTheory.IsAddFundamentalDomain Λ T)
    (hS : MeasurableSet S) (hSf : MeasureTheory.volume S ≠ ⊤) :
    MeasureTheory.Integrable (fun a =>
      (∑' l : Λ, S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)).toReal)
      (MeasureTheory.volume.restrict T) ∧
    (∫ a in T, (∑' l : Λ,
      S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)).toReal) =
        (MeasureTheory.volume S).toReal := by
  classical
  letI : AddAction Λ (Fin f → ℂ) :=
    { vadd := fun l a => (l : Fin f → ℂ) + a
      zero_vadd := by intro a; exact zero_add a
      add_vadd := by intro l k a; exact add_assoc _ _ _ }
  letI : MeasurableConstVAdd Λ (Fin f → ℂ) :=
    ⟨fun l => measurable_const.add measurable_id⟩
  letI : MeasureTheory.VAddInvariantMeasure Λ (Fin f → ℂ) MeasureTheory.volume :=
    ⟨fun l S hS => MeasureTheory.measure_preimage_add MeasureTheory.volume (l : Fin f → ℂ) S⟩
  have hm : ∀ l : Λ, Measurable (fun a =>
      S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)) := by
    intro l
    exact (measurable_const.indicator hS).comp (measurable_const.add measurable_id)
  have hsum := Measurable.ennreal_tsum hm
  have hi : (∫⁻ a in T, ∑' l : Λ,
      S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)) =
      MeasureTheory.volume S := by
    rw [MeasureTheory.lintegral_tsum (fun l => (hm l).aemeasurable)]
    have hunfold := hT.lintegral_eq_tsum'' (S.indicator (fun _ => (1 : ENNReal)))
    change (∫⁻ a, S.indicator (fun _ => (1 : ENNReal)) a) =
      (∑' l : Λ, ∫⁻ a in T, S.indicator (fun _ => (1 : ENNReal))
        ((l : Fin f → ℂ) + a)) at hunfold
    rw [← hunfold]
    simp [MeasureTheory.lintegral_indicator hS]
  have hfinite : (∫⁻ a in T, ∑' l : Λ,
      S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)) ≠ ⊤ := hi.trans_ne hSf
  exact ⟨MeasureTheory.integrable_toReal_of_lintegral_ne_top hsum.aemeasurable hfinite,
    (MeasureTheory.integral_toReal hsum.aemeasurable
      (MeasureTheory.ae_lt_top hsum hfinite)).trans (congrArg ENNReal.toReal hi)⟩

lemma coset_count_eq_indicator_sum {f : ℕ} (Λ : Submodule ℤ (Fin f → ℂ))
    (a : Fin f → ℂ) (S : Set (Fin f → ℂ)) :
    (Nat.card {z : Fin f → ℂ // z - a ∈ Λ ∧ z ∈ S} : ℝ) =
      (∑' l : Λ, S.indicator (fun _ => (1 : ENNReal)) ((l : Fin f → ℂ) + a)).toReal := by
  classical
  let e : {z : Fin f → ℂ // z - a ∈ Λ ∧ z ∈ S} ≃
      {l : Λ // (l : Fin f → ℂ) + a ∈ S} :=
    { toFun := fun z => ⟨⟨z.val - a, z.property.1⟩, by simpa using z.property.2⟩
      invFun := fun l => ⟨(l.val : Fin f → ℂ) + a,
        by simpa using l.val.property, l.property⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro l; apply Subtype.ext; apply Subtype.ext; simp }
  rw [Nat.card_congr e]
  change (Nat.card ({l : Λ | (l : Fin f → ℂ) + a ∈ S} : Set Λ) : ℝ) = _
  rw [real_count_eq_indicator_sum]
  congr 1

lemma finite_coset_section {f m : ℕ} (b : Module.Basis (Fin m) ℝ (Fin f → ℂ))
    (a : Fin f → ℂ) {S : Set (Fin f → ℂ)} (hS : Bornology.IsBounded S) :
    Set.Finite {z : Fin f → ℂ | z - a ∈ Submodule.span ℤ (Set.range b) ∧ z ∈ S} := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS
  apply Set.Finite.of_injOn (f := fun z => z - a) (t :=
    Metric.closedBall 0 (C + ‖a‖) ∩ (Submodule.span ℤ (Set.range b) : Set (Fin f → ℂ)))
  · intro z hz
    refine ⟨?_, hz.1⟩
    have hzC : ‖z‖ ≤ C := by simpa using hC hz.2
    simpa using (norm_sub_le z a).trans (add_le_add hzC le_rfl)
  · exact (sub_left_injective).injOn
  · exact ZSpan.setFinite_inter b Metric.isBounded_closedBall

lemma unit_overlap_volume (u : ℂ) (hu : ‖u‖ = 1) (R : ℝ) :
    MeasureTheory.volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R} =
      MeasureTheory.volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R) := by
  have hu0 : -u ≠ 0 := neg_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hu]; norm_num))
  let l : ℂ →ₗᵢ[ℝ] ℂ :=
    { toLinearMap :=
        { toFun := fun z => -u * z
          map_add' := fun x y => mul_add _ _ _
          map_smul' := by intro r z; simp [Algebra.smul_def, mul_left_comm] }
      norm_map' := by intro z; simp [norm_mul, hu] }
  let e := LinearIsometryEquiv.ofSurjective l (fun z =>
    ⟨(-u)⁻¹ * z, by change -u * ((-u)⁻¹ * z) = z; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]⟩)
  have he : ∀ z, e z = -u * z := fun _ => rfl
  have hpre : e ⁻¹' {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R} =
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R := by
    ext z
    have hz : -u * z + u = -u * (z - 1) := by ring
    change (‖-u * z‖ ≤ R ∧ ‖-u * z + u‖ ≤ R) ↔ _
    rw [hz]
    simp [norm_mul, hu, Metric.mem_closedBall, dist_eq_norm]
  have hm : MeasurableSet {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R} := by
    exact (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (isClosed_le (continuous_id.add continuous_const).norm continuous_const).measurableSet
  rw [← hpre]
  exact (e.measurePreserving.measure_preimage hm.nullMeasurableSet).symm

lemma polydisc_volume (f : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (MeasureTheory.volume {z : Fin f → ℂ | ∀ j, ‖z j‖ ≤ R}).toReal =
      (Real.pi * R ^ 2) ^ f := by
  have hset : {z : Fin f → ℂ | ∀ j, ‖z j‖ ≤ R} =
      Set.pi Set.univ (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hset, MeasureTheory.volume_pi_pi]
  simp [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR, mul_comm]

lemma polydisc_overlap_volume {f : ℕ} (u : Fin f → ℂ) (hu : ∀ j, ‖u j‖ = 1) (R : ℝ) :
    (MeasureTheory.volume {z : Fin f → ℂ | (∀ j, ‖z j‖ ≤ R) ∧
      ∀ j, ‖z j + u j‖ ≤ R}).toReal =
    (MeasureTheory.volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall 1 R)).toReal ^ f := by
  have hset : {z : Fin f → ℂ | (∀ j, ‖z j‖ ≤ R) ∧ ∀ j, ‖z j + u j‖ ≤ R} =
      Set.pi Set.univ (fun j : Fin f => {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u j‖ ≤ R}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact forall_and.symm
  rw [hset, MeasureTheory.volume_pi_pi]
  simp_rw [unit_overlap_volume _ (hu _) R]
  simp

lemma ordered_edge_count {V K : Type*} [AddCommGroup V] (X : Set V) (hX : X.Finite)
    (U : Finset K) (φ : K → V) (hφ : Function.Injective φ) :
    Nat.card {e : V × V // e.1 ∈ X ∧ e.2 ∈ X ∧ ∃ u ∈ U, e.2 - e.1 = φ u} =
      ∑ u : U, Nat.card {z : V // z ∈ X ∧ z + φ u ∈ X} := by
  classical
  let Y := {e : V × V // e.1 ∈ X ∧ e.2 ∈ X ∧ ∃ u ∈ U, e.2 - e.1 = φ u}
  let pick : Y → U := fun e =>
    ⟨e.property.2.2.choose, e.property.2.2.choose_spec.1⟩
  have hpick : ∀ e : Y, e.val.2 - e.val.1 = φ (pick e) :=
    fun e => e.property.2.2.choose_spec.2
  let g : Y → (u : U) × {z : V // z ∈ X ∧ z + φ u ∈ X} := fun e =>
    ⟨pick e, ⟨e.val.1, e.property.1, by
      rw [← hpick e]
      convert e.property.2.1 using 1 <;> abel⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro e d h
      have hu : pick e = pick d := congrArg Sigma.fst h
      have hz : e.val.1 = d.val.1 := congrArg (fun v => v.2.val) h
      apply Subtype.ext
      apply Prod.ext hz
      have he := hpick e
      have hd := hpick d
      rw [hu, hz] at he
      exact sub_left_injective (he.trans hd.symm)
    · rintro ⟨u, z⟩
      let e : Y := ⟨(z.val, z.val + φ u), z.property.1, z.property.2,
        u.val, u.property, by simp⟩
      have hu : pick e = u := by
        apply Subtype.ext
        apply hφ
        simpa [e] using (hpick e).symm
      refine ⟨e, ?_⟩
      apply Sigma.ext hu
      exact (Subtype.heq_iff_coe_eq (fun w => by
        change (w ∈ X ∧ w + φ (pick e) ∈ X) ↔ (w ∈ X ∧ w + φ u ∈ X)
        rw [hu])).mpr rfl
  letI : Finite X := hX.to_subtype
  letI : ∀ u : U, Finite {z : V // z ∈ X ∧ z + φ u ∈ X} := fun u =>
    Finite.of_injective (fun z => (⟨z.val, z.property.1⟩ : X))
      (fun z w h => Subtype.ext (congrArg (fun x : X => x.val) h))
  exact (Nat.card_eq_of_bijective g hg).trans Nat.card_sigma

lemma window_coset_mem {A : UnitDistance.AdmissibleDatum} (W : UnitDistance.MinkowskiWindow A)
    (Λ : Submodule ℤ (Fin (Module.finrank ℚ A.L) → ℂ))
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ x : A.K,
      IsIntegral ℤ ((UnitDistance.admissibleDenominator A : A.K) * x) ∧
      ∀ j, z j = W.σ j x) (a z : Fin (Module.finrank ℚ A.L) → ℂ) :
    (∃ x : A.K, IsIntegral ℤ ((UnitDistance.admissibleDenominator A : A.K) * x) ∧
      ∀ j, z j = a j + W.σ j x) ↔ z - a ∈ Λ := by
  rw [hΛ]
  constructor
  · rintro ⟨x, hx, hz⟩
    refine ⟨x, hx, fun j => ?_⟩
    change z j - a j = W.σ j x
    rw [hz j]
    abel
  · rintro ⟨x, hx, hz⟩
    refine ⟨x, hx, fun j => ?_⟩
    have hj : z j - a j = W.σ j x := hz j
    rw [← hj]
    abel



end Formalization.Result.helpers.Lemma_2p4.Machinery
