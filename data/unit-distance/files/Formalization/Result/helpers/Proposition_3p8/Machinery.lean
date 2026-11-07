import Formalization.Axioms
import Formalization.Definition
import Formalization.Result.Proposition_3p2
import Formalization.Result.Proposition_3p6
import Formalization.Result.Proposition_3p7
import Formalization.Result.Proposition_Ap13
import Mathlib

namespace Formalization.Result.helpers.Proposition_3p8.Machinery



lemma prime_log_bound {C : ℝ} (hC : 1 ≤ C) {ell : ℕ} (hell : 2 ≤ ell)
    {r : ℕ} (hr : 0 < r)
    (hbound : (r : ℝ) ≤ C * ell * Real.log (2 * ell)) :
    Real.log r ≤ (Real.log (2 * C) / Real.log 2 + 2) * Real.log ell := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hepos : (0 : ℝ) < ell := by linarith
  have hCpos : 0 < C := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hlogell : Real.log 2 ≤ Real.log ell := Real.log_le_log (by norm_num) he
  have hr' : (r : ℝ) ≤ 2 * C * (ell : ℝ) ^ 2 := by
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * ell by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * ell by positivity)]
  calc
    Real.log r ≤ Real.log (2 * C * (ell : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hr) hr'
    _ = Real.log (2 * C) + 2 * Real.log ell := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num
    _ ≤ (Real.log (2 * C) / Real.log 2 + 2) * Real.log ell := by
      have h := mul_le_mul_of_nonneg_left hlogell
        (div_nonneg hlogC hlog2.le)
      rw [div_mul_cancel₀ _ hlog2.ne'] at h
      nlinarith

lemma cubic_log_root_bound (F : Type) [Field F] [NumberField F]
    (ell : ℕ) (r : Fin ell → ℕ) (hpos : ∀ j, 0 < r j)
    (hdeg : Module.finrank ℚ F = 3)
    (hdisc : UnitDistance.absoluteDiscriminant F = (∏ j, r j) ^ 2)
    (B : ℝ) (hB : 0 ≤ B) (hell : 2 ≤ ell)
    (hlog : ∀ j, Real.log (r j) ≤ B * Real.log ell) :
    Real.log (UnitDistance.rootDiscriminant F) ≤ B * ell * Real.log ell := by
  have hp : (0 : ℝ) < ∏ j, (r j : ℝ) :=
    Finset.prod_pos (fun j _ => by exact_mod_cast hpos j)
  have hs : ∑ j, Real.log (r j) ≤ (ell : ℝ) * (B * Real.log ell) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hlog j)
  have hsum : 0 ≤ ∑ j, Real.log (r j) :=
    Finset.sum_nonneg (fun j _ => Real.log_natCast_nonneg _)
  unfold UnitDistance.rootDiscriminant
  rw [hdeg, hdisc, Nat.cast_pow, Nat.cast_prod,
    Real.log_rpow (by positivity), Real.log_pow,
    Real.log_prod (fun j _ => (show (0 : ℝ) < r j by exact_mod_cast hpos j).ne')]
  norm_num
  nlinarith

lemma no_cubic_root_of_totallyReal (F : Type) [Field F] [NumberField F]
    (hreal : UnitDistance.totallyReal F) :
    ¬ ∃ ζ : F, IsPrimitiveRoot ζ 3 := by
  rintro ⟨ζ, hζ⟩
  let σ : F →+* ℂ := Classical.choice inferInstance
  have hζ' := hζ.map_of_injective σ.injective
  have hcube : (σ ζ).re ^ 3 = 1 := by
    have h := congrArg Complex.re hζ'.pow_eq_one
    simpa [pow_succ, Complex.mul_re, Complex.mul_im, hreal σ ζ] using h
  have hroot : (σ ζ).re = 1 := by nlinarith [sq_nonneg ((σ ζ).re + 1 / 2)]
  have hone : σ ζ = 1 := by
    apply Complex.ext
    · simpa using hroot
    · simpa using hreal σ ζ
  have := hζ'.ne_one (by norm_num : 1 < 3)
  exact this hone

lemma root_discriminant_ge_one (F : Type) [Field F] [NumberField F] :
    1 ≤ UnitDistance.rootDiscriminant F := by
  have hpos := Formalization.Result.helpers.Proposition_Ap13.Machinery.discriminant_pos F
  apply Real.one_le_rpow
  · exact_mod_cast hpos
  · positivity

lemma quadratic_floor_lower_bound (ell : ℕ) (hell : 100 ≤ ell) :
    (ell : ℝ) ^ 2 / 200 ≤ (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) := by
  have he : (100 : ℝ) ≤ ell := by exact_mod_cast hell
  have hsub : ((ell - 1 : ℕ) : ℝ) = ell - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ell), Nat.cast_one]
  have h := Nat.mod_lt ((ell - 1) ^ 2) (by norm_num : 0 < 100)
  have hd := Nat.mod_add_div ((ell - 1) ^ 2) 100
  have h' : (((ell - 1) ^ 2 % 100 : ℕ) : ℝ) < 100 := by exact_mod_cast h
  have hd' : (((ell - 1) ^ 2 % 100 : ℕ) : ℝ) +
      100 * (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) = ((ell : ℝ) - 1) ^ 2 := by
    rw [← hsub]
    exact_mod_cast hd
  nlinarith [sq_nonneg ((ell : ℝ) - 2)]

lemma eventual_positive_translation_bound (C : ℝ) (hC : 0 < C) :
    ∃ ell₀ : ℕ, 100 ≤ ell₀ ∧ ∀ ell : ℕ, ell₀ ≤ ell →
      C * ell * Real.log ell < (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound
    (show 0 < Real.log 2 / (400 * C) by positivity)
  have hn := Filter.Tendsto.eventually
    (tendsto_natCast_atTop_atTop (R := ℝ)) hsmall
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hn
  refine ⟨max n 100, le_max_right _ _, ?_⟩
  intro ell hell
  have he100 : 100 ≤ ell := (le_max_right n 100).trans hell
  have he : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have h := hn ell ((le_max_left n 100).trans hell)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg ell),
    abs_of_nonneg he.le] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ C * ell by positivity)
  have hcancel : C * ell * (Real.log 2 / (400 * C) * ell) =
      Real.log 2 * (ell : ℝ) ^ 2 / 400 := by field_simp <;> ring
  have hfloor := quadratic_floor_lower_bound ell he100
  have hfloor' := mul_le_mul_of_nonneg_right hfloor hlog2.le
  rw [hcancel] at hmul
  nlinarith [sq_pos_of_pos he]

lemma cutting_relation_inequality (ell d r s : ℕ) (C₀ : ℝ)
    (hell : 11 ≤ ell) (hC₀ : C₀ ≤ (ell - 1 : ℕ))
    (hd : ell - 1 ≤ d) (hr : (r : ℝ) ≤ d + C₀)
    (hs : s ≤ r + 3 * ((ell - 1) ^ 2 / 100)) :
    4 * s ≤ d ^ 2 := by
  have he : 10 ≤ d := by omega
  have he' : (10 : ℝ) ≤ d := by exact_mod_cast he
  have hC : C₀ ≤ (d : ℝ) := hC₀.trans (by exact_mod_cast hd)
  have ht : 100 * ((ell - 1) ^ 2 / 100) ≤ d ^ 2 :=
    (Nat.mul_div_le _ _).trans (Nat.pow_le_pow_left hd 2)
  have ht' : 100 * (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast ht
  have hs' : (s : ℝ) ≤ r + 3 * (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) := by
    exact_mod_cast hs
  have hquad : 10 * (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hfinal : 4 * (s : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hfinal

lemma enumerate_split_primes (F : Type) [Field F] [NumberField F]
    (q : ℕ) (hq : UnitDistance.completelySplit ℚ F
      (Ideal.span {(q : NumberField.RingOfIntegers ℚ)})) :
    ∃ p : Fin (Module.finrank ℚ F) → Ideal (NumberField.RingOfIntegers F),
      (∀ a, p a ≠ ⊥ ∧ (p a).IsPrime ∧
        (p a).comap (algebraMap (NumberField.RingOfIntegers ℚ)
          (NumberField.RingOfIntegers F)) = Ideal.span {(q : NumberField.RingOfIntegers ℚ)}) ∧
      ∀ P : Ideal (NumberField.RingOfIntegers F), P.IsPrime →
        P.comap (algebraMap (NumberField.RingOfIntegers ℚ)
          (NumberField.RingOfIntegers F)) = Ideal.span {(q : NumberField.RingOfIntegers ℚ)} →
        ∃ a, p a = P := by
  classical
  let S := {P : Ideal (NumberField.RingOfIntegers F) // P.IsPrime ∧
    P.comap (algebraMap (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers F)) = Ideal.span {(q : NumberField.RingOfIntegers ℚ)}}
  have hcard : Nat.card S = Module.finrank ℚ F := hq.2.2.1
  let e : S ≃ Fin (Module.finrank ℚ F) :=
    (Nat.equivFinOfCardPos (hcard ▸ Module.finrank_pos.ne')).trans (finCongr hcard)
  refine ⟨fun a => (e.symm a).val, ?_, ?_⟩
  · intro a
    refine ⟨?_, (e.symm a).property⟩
    intro hp
    change (e.symm a).val = ⊥ at hp
    have h := (e.symm a).property.2
    rw [hp, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers ℚ)
        (NumberField.RingOfIntegers F))] at h
    exact hq.1 h.symm
  · intro P hP hmap
    exact ⟨e ⟨P, hP, hmap⟩, congrArg Subtype.val (e.symm_apply_apply _)⟩

lemma unramified_root_discriminant (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M] [IsScalarTower ℚ F M]
    (hu : UnitDistance.everywhereUnramified F M) :
    UnitDistance.rootDiscriminant M = UnitDistance.rootDiscriminant F := by
  have htop : UnitDistance.relativeDiscriminant F M = ⊤ :=
    (UnitDistance.discriminantAndSplittingFacts.1 F M).2.mpr hu.1
  have hdisc := (UnitDistance.discriminantAndSplittingFacts.1 F M).1
  rw [htop, Ideal.absNorm_top, mul_one] at hdisc
  apply (pow_left_inj₀
    (Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pos M).le
    (Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pos F).le
    (Module.finrank_pos (R := ℚ) (M := M)).ne').mp
  rw [Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree,
    hdisc, Nat.cast_pow, ← Module.finrank_mul_finrank ℚ F M, pow_mul,
    Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree]

lemma principal_nat_norm (F : Type) [Field F] [NumberField F] (n : ℕ) :
    (Ideal.span {(n : NumberField.RingOfIntegers F)}).absNorm = n ^ Module.finrank ℚ F := by
  rw [Ideal.absNorm_span_singleton]
  have h := Algebra.norm_algebraMap_of_basis
    (Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers F)) (n : ℤ)
  simp only [map_natCast] at h
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers F)) = Module.finrank ℚ F := by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ
      (NumberField.RingOfIntegers F)), NumberField.RingOfIntegers.rank]
  rw [h, hc]
  simp

lemma quadratic_cm_root_bound (A : UnitDistance.AdmissibleDatum) :
    UnitDistance.rootDiscriminant A.K ≤ 2 * UnitDistance.rootDiscriminant A.L := by
  letI : IsScalarTower ℚ A.L A.K := IsScalarTower.of_algebraMap_eq
    (fun x => by simp)
  obtain ⟨hrel, hdeg, _⟩ := UnitDistance.idealArithmeticFacts.2
    A.L A.K A.realL A.i A.i_sq A.generated A.c A.c_ne_one
  have hdiv := (UnitDistance.discriminantAndSplittingFacts.2.2.1
    A.L A.K A.realL A.i A.i_sq A.generated).1
  have hnorm := map_dvd Ideal.absNorm hdiv
  have hfour := principal_nat_norm A.L 4
  norm_num only [Nat.cast_ofNat] at hfour
  rw [hfour] at hnorm
  have hnormle := Nat.le_of_dvd (by positivity : 0 < 4 ^ Module.finrank ℚ A.L) hnorm
  have hdisc := (UnitDistance.discriminantAndSplittingFacts.1 A.L A.K).1
  rw [hrel] at hdisc
  have hdisc_bound : UnitDistance.absoluteDiscriminant A.K ≤
      UnitDistance.absoluteDiscriminant A.L ^ 2 * 4 ^ Module.finrank ℚ A.L := by
    rw [hdisc]
    exact Nat.mul_le_mul_left _ hnormle
  apply le_of_pow_le_pow_left₀ (Module.finrank_pos (R := ℚ) (M := A.K)).ne'
    (by have := root_discriminant_ge_one A.L; positivity)
  rw [Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree]
  have hpow : (2 * UnitDistance.rootDiscriminant A.L) ^ Module.finrank ℚ A.K =
      (UnitDistance.absoluteDiscriminant A.L : ℝ) ^ 2 * 4 ^ Module.finrank ℚ A.L := by
    rw [hdeg, mul_pow, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num,
      mul_comm 2 (Module.finrank ℚ A.L), pow_mul,
      Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree,
      mul_comm]
  rw [hpow]
  exact_mod_cast hdisc_bound

lemma class_bound_with_fixed_root (K : Type) [Field K] [NumberField K]
    (C R : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R) (f : ℕ)
    (hdeg : Module.finrank ℚ K = 2 * f)
    (hroot : UnitDistance.rootDiscriminant K ≤ 2 * R)
    (hclass : (UnitDistance.classNumber K : ℝ) ≤
      max 2 (UnitDistance.rootDiscriminant K) ^ (C * Module.finrank ℚ K)) :
    (UnitDistance.classNumber K : ℝ) ≤ ((2 * R) ^ (2 * C)) ^ f := by
  calc
    (UnitDistance.classNumber K : ℝ) ≤
        max 2 (UnitDistance.rootDiscriminant K) ^ (C * Module.finrank ℚ K) := hclass
    _ ≤ (2 * R) ^ (C * Module.finrank ℚ K) := by
      apply Real.rpow_le_rpow (by positivity) (max_le (by linarith) hroot) (by positivity)
    _ = ((2 * R) ^ (2 * C)) ^ f := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hdeg, Nat.cast_mul, Nat.cast_ofNat]
      congr 1
      ring

lemma log_class_constant_bound (R C B : ℝ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (ell : ℕ) (hell : 2 ≤ ell)
    (hlog : Real.log R ≤ B * ell * Real.log ell) :
    Real.log ((2 * R) ^ (2 * C)) ≤ 2 * C * (1 + B) * ell * Real.log ell := by
  have he : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hl : Real.log 2 ≤ Real.log ell := Real.log_le_log (by norm_num) (by exact_mod_cast hell)
  have hl' : Real.log ell ≤ (ell : ℝ) * Real.log ell :=
    le_mul_of_one_le_left (Real.log_natCast_nonneg ell) he
  rw [Real.log_rpow (by positivity), Real.log_mul (by norm_num) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (hl.trans hl') hlog)
    (show 0 ≤ 2 * C by positivity)]

lemma finite_topological_generating_set (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (d : ℕ) (hd : UnitDistance.generatorRank G = (d : ℕ∞)) :
    ∃ S : Finset G, S.card = d ∧
      (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  classical
  let T : Set ℕ∞ := {n | ∃ S : Finset G, (S.card : ℕ∞) = n ∧
    (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}
  have hT : T.Nonempty := by
    by_contra h
    have h' : T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    change sInf T = (d : ℕ∞) at hd
    rw [h', sInf_empty] at hd
    exact ENat.coe_ne_top d hd.symm
  have hmem : UnitDistance.generatorRank G ∈ T := csInf_mem hT
  rw [hd] at hmem
  obtain ⟨S, hS, htop⟩ := hmem
  exact ⟨S, by exact_mod_cast hS, htop⟩

lemma elementary_quotient_rank_bound (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n d : ℕ)
    (f : G →* Multiplicative (Fin n → ZMod 3))
    (hf : Function.Surjective f) (hcont : Continuous f)
    (hd : UnitDistance.generatorRank G = (d : ℕ∞)) : n ≤ d := by
  classical
  obtain ⟨S, hS, htop⟩ := finite_topological_generating_set G d hd
  let T : Finset (Fin n → ZMod 3) := S.image (fun g => (f g).toAdd)
  let V : Submodule (ZMod 3) (Fin n → ZMod 3) := Submodule.span (ZMod 3) (T : Set _)
  let U : Subgroup G := V.toAddSubgroup.toSubgroup.comap f
  have hUclosed : IsClosed (U : Set G) := by
    change IsClosed (f ⁻¹' (V.toAddSubgroup.toSubgroup : Set (Multiplicative (Fin n → ZMod 3))))
    exact (Set.toFinite _).isClosed.preimage hcont
  have hSU : Subgroup.closure (S : Set G) ≤ U := by
    apply (Subgroup.closure_le U).mpr
    intro g hg
    change (f g).toAdd ∈ V
    exact Submodule.subset_span (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hUtop : U = ⊤ := top_unique (htop ▸
    (Subgroup.closure (S : Set G)).topologicalClosure_minimal hSU hUclosed)
  have hV : V = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    obtain ⟨g, hg⟩ := hf (Multiplicative.ofAdd y)
    have hmem : g ∈ U := hUtop ▸ Subgroup.mem_top g
    change (f g).toAdd ∈ V at hmem
    simpa [hg] using hmem
  have hdim := finrank_span_finset_le_card (R := ZMod 3) T
  change Module.finrank (ZMod 3) V ≤ T.card at hdim
  rw [hV, finrank_top] at hdim
  have hn : Module.finrank (ZMod 3) (Fin n → ZMod 3) = n := by simp
  rw [hn] at hdim
  exact hdim.trans ((Finset.card_image_le).trans_eq hS)

lemma exists_smaller_open_normal (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Infinite G] (H : OpenNormalSubgroup G) :
    ∃ K : OpenNormalSubgroup G, K < H := by
  classical
  letI : H.toSubgroup.FiniteIndex := H.toOpenSubgroup.finiteIndex_of_finite_quotient
  have hH : H.toSubgroup ≠ ⊥ := by
    intro h
    haveI : Finite H.toSubgroup := by rw [h]; infer_instance
    haveI : Finite G := (Subgroup.finite_iff_finite_and_finiteIndex H.toSubgroup).mpr
      ⟨inferInstance, inferInstance⟩
    exact not_finite G
  obtain ⟨xH, hxH⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  let x : G := xH.val
  have hx : x ∈ H := xH.property
  have hxne : x ≠ 1 := fun h => hxH (Subtype.ext h)
  obtain ⟨K, hK⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isClosed_singleton (x := x)).isOpen_compl (by simpa using Ne.symm hxne)
  refine ⟨H ⊓ K, lt_of_le_of_ne inf_le_left ?_⟩
  intro heq
  have hxK : x ∈ K := (show x ∈ H ⊓ K from heq.symm ▸ hx).2
  exact hK hxK (Set.mem_singleton x)

lemma embedded_elementary_quotient_rank_bound
    (F M Ω : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (n d : ℕ) (e : M →ₐ[F] Ω)
    (eM : (M ≃ₐ[F] M) ≃* (Fin n → Multiplicative (ZMod 3)))
    (hd : UnitDistance.generatorRank (Ω ≃ₐ[F] Ω) = (d : ℕ∞)) : n ≤ d := by
  classical
  let E := e.fieldRange
  let ee : M ≃ₐ[F] E := AlgEquiv.ofInjective e e.injective
  letI : FiniteDimensional F E := Module.Finite.equiv ee.toLinearEquiv
  letI : IsGalois F E := IsGalois.of_algEquiv ee
  let toVector : (Fin n → Multiplicative (ZMod 3)) ≃*
      Multiplicative (Fin n → ZMod 3) :=
    { toFun := fun x => Multiplicative.ofAdd (fun j => (x j).toAdd)
      invFun := fun x j => Multiplicative.ofAdd (x.toAdd j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let eGal := (AlgEquiv.autCongr ee).symm.trans (eM.trans toVector)
  let ρ : (Ω ≃ₐ[F] Ω) →* (E ≃ₐ[F] E) := AlgEquiv.restrictNormalHom E
  let f := eGal.toMonoidHom.comp ρ
  apply elementary_quotient_rank_bound (Ω ≃ₐ[F] Ω) n d f
    (eGal.surjective.comp (AlgEquiv.restrictNormalHom_surjective Ω)) ?_ hd
  exact (continuous_of_discreteTopology (f := eGal)).comp
    (InfiniteGalois.restrictNormalHom_continuous E)

lemma quotient_totally_disconnected (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  classical
  have separate_one (z : G ⧸ N) (hz : z ≠ 1) :
      ∃ U : OpenSubgroup (G ⧸ N), z ∉ U := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have hg : g ∉ N := fun h => hz ((QuotientGroup.eq_one_iff g).mpr h)
    have hmeet := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨N, hN⟩ : ClosedSubgroup G)
    have hex : ∃ H : Subgroup G, IsOpen (H : Set G) ∧ N ≤ H ∧ g ∉ H := by
      by_contra h
      push_neg at h
      apply hg
      change g ∈ (⟨N, hN⟩ : ClosedSubgroup G).toSubgroup
      rw [hmeet]
      apply Subgroup.mem_sInf.mpr
      intro H hH
      exact h H hH.1 hH.2
    obtain ⟨H, hHopen, hNH, hgH⟩ := hex
    let U : Subgroup (G ⧸ N) := H.map (QuotientGroup.mk' N)
    have hUopen : IsOpen (U : Set (G ⧸ N)) :=
      QuotientGroup.isOpenMap_coe (H : Set G) hHopen
    refine ⟨⟨U, hUopen⟩, ?_⟩
    intro h
    change g ∈ U.comap (QuotientGroup.mk' N) at h
    have hpre : U.comap (QuotientGroup.mk' N) = H :=
      Subgroup.comap_map_eq_self (by simpa using hNH)
    exact hgH (hpre ▸ h)
  haveI : TotallySeparatedSpace (G ⧸ N) :=
    totallySeparatedSpace_iff_exists_isClopen.mpr (by
      intro x y hxy
      obtain ⟨U, hU⟩ := separate_one (x⁻¹ * y) (by
        intro h
        apply hxy.symm
        simpa [← mul_assoc] using congrArg (fun z => x * z) h)
      refine ⟨(fun z => x⁻¹ * z) ⁻¹' (U : Set (G ⧸ N)),
        U.isClopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
      · simpa using U.one_mem
      · exact hU)
  infer_instance

lemma pro_three_of_continuous_surjection (G H : ProfiniteGrp.{0})
    (hpro : ∀ (N : Subgroup G) (hN : N.Normal), IsOpen (N : Set G) →
      letI := hN
      IsPGroup 3 (G ⧸ N))
    (π : ContinuousMonoidHom G H) (hπ : Function.Surjective π) :
    ∀ (N : Subgroup H) (hN : N.Normal), IsOpen (N : Set H) →
      letI := hN
      IsPGroup 3 (H ⧸ N) := by
  intro N hN hopen
  letI := hN
  let f : G →* H ⧸ N := (QuotientGroup.mk' N).comp π.toMonoidHom
  have hf : Function.Surjective f := QuotientGroup.mk_surjective.comp hπ
  have hker : f.ker = N.comap π.toMonoidHom := by
    change ((QuotientGroup.mk' N).comp π.toMonoidHom).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hkeropen : IsOpen (f.ker : Set G) := by
    rw [hker]
    exact hopen.preimage π.continuous
  exact (hpro f.ker inferInstance hkeropen).of_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

lemma nontrivial_of_positive_generator_rank (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (d : ℕ) (hdpos : 0 < d)
    (hd : UnitDistance.generatorRank G = (d : ℕ∞)) : Nontrivial G := by
  classical
  by_contra h
  haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp h
  have hz : UnitDistance.generatorRank G ≤ 0 := by
    apply sInf_le
    refine ⟨∅, by simp, ?_⟩
    exact Subsingleton.elim _ _
  rw [hd] at hz
  have hdle : d ≤ 0 := by exact_mod_cast hz
  omega

lemma no_square_neg_one (L : Type) [Field L] [NumberField L]
    (hreal : UnitDistance.totallyReal L) (x : L) : x ^ 2 ≠ -1 := by
  intro hx
  let σ : L →+* ℂ := Classical.choice inferInstance
  have h := congrArg (fun z => (σ z).re) hx
  simp only [map_pow, map_neg, map_one, Complex.neg_re, Complex.one_re] at h
  rw [pow_two, Complex.mul_re, hreal σ x] at h
  nlinarith [sq_nonneg (σ x).re]

lemma exists_imaginary_quadratic_extension (L : Type) [Field L] [NumberField L]
    (hreal : UnitDistance.totallyReal L) :
    ∃ (K : Type) (hK : Field K),
      letI := hK
      ∃ hNK : NumberField K,
        letI := hNK
        ∃ hLK : Algebra L K,
          letI := hLK
          ∃ (i : K) (c : K ≃ₐ[L] K),
            i ^ 2 = -1 ∧ Algebra.adjoin L {i} = ⊤ ∧ c ≠ 1 := by
  classical
  let P : Polynomial L := Polynomial.X ^ 2 + Polynomial.C 1
  have hPmonic : P.Monic := Polynomial.monic_X_pow_add_C 1 (by norm_num)
  have hPdeg : P.natDegree = 2 := by dsimp [P]; compute_degree!
  have hPirred : Irreducible P := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hPdeg]; decide)
    intro x hx
    have h : x ^ 2 + 1 = 0 := by simpa [P, Polynomial.IsRoot] using hx
    exact no_square_neg_one L hreal x (eq_neg_of_add_eq_zero_left h)
  letI : Fact (Irreducible P) := ⟨hPirred⟩
  let K := AdjoinRoot P
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap L K).injective
  letI : Module.Finite L K := hPmonic.finite_adjoinRoot
  letI : Module.Finite ℚ K := Module.Finite.trans (R := ℚ) L K
  letI : NumberField K := { to_finiteDimensional := inferInstance }
  let i : K := AdjoinRoot.root P
  have hi : i ^ 2 = -1 := by
    have h : i ^ 2 + 1 = 0 := by
      simpa [P, i, Polynomial.eval₂_add, Polynomial.eval₂_pow] using AdjoinRoot.eval₂_root P
    exact eq_neg_of_add_eq_zero_left h
  have hminus : P.eval₂ (Algebra.ofId L K) (-i) = 0 := by
    change (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial L).eval₂
      (Algebra.ofId L K).toRingHom (-i) = 0
    rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_one, neg_sq, hi, neg_add_cancel]
  let cHom : K →ₐ[L] K := AdjoinRoot.liftAlgHom P (Algebra.ofId L K) (-i) hminus
  let c : K ≃ₐ[L] K := AlgEquiv.ofBijective cHom
    ⟨cHom.injective, LinearMap.surjective_of_injective (f := cHom.toLinearMap) cHom.injective⟩
  have hcroot : c i = -i := AdjoinRoot.liftAlgHom_root P (Algebra.ofId L K) (-i) hminus
  have hc : c ≠ 1 := by
    intro hc
    have hneg : -i = i := hcroot.symm.trans (by rw [hc]; rfl)
    have hzero : (2 : K) * i = 0 := by linear_combination -hneg
    have hi0 : i = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    rw [hi0] at hi
    norm_num at hi
  exact ⟨K, inferInstance, inferInstance, inferInstance, i, c,
    hi, AdjoinRoot.adjoinRoot_eq_top (f := P), hc⟩

lemma unramified_of_equal_root_discriminant (F M : Type)
    [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    [IsScalarTower ℚ F M] (hreal : UnitDistance.totallyReal M)
    (hroot : UnitDistance.rootDiscriminant M = UnitDistance.rootDiscriminant F) :
    UnitDistance.everywhereUnramified F M := by
  apply Formalization.Result.helpers.Proposition_3p2.Machinery.unramified_of_discriminant_norm_one
    F M _ hreal
  apply Formalization.Result.helpers.Proposition_3p2.Machinery.norm_relativeDiscriminant_eq_one
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_pow,
    ← Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree M,
    ← Formalization.Result.helpers.Proposition_Ap13.Machinery.root_discriminant_pow_degree F,
    hroot, ← pow_mul, Module.finrank_mul_finrank ℚ F M]

lemma frobenius_class_singleton_of_identity (F M : Type)
    [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M] [IsGalois F M]
    (p : Ideal (NumberField.RingOfIntegers F))
    (hone : (1 : M ≃ₐ[F] M) ∈ UnitDistance.frobeniusClass F M p) :
    UnitDistance.frobeniusClass F M p = {1} := by
  classical
  let R := NumberField.RingOfIntegers F
  let S := NumberField.RingOfIntegers M
  let G := M ≃ₐ[F] M
  letI : MulSemiringAction G S := IsIntegralClosure.MulSemiringAction R F M S
  letI : SMulCommClass G R S := ⟨fun σ a x => (galRestrict R F M S σ).toLinearEquiv.map_smul a x⟩
  letI : Algebra.IsInvariant R S G := Algebra.isInvariant_of_isGalois R F M S
  have hp : p ≠ ⊥ := hone.1
  have compare (σ : G) (P : Ideal S) (hP : P.IsPrime)
      (hmap : P.comap (algebraMap R S) = p) (he : p.ramificationIdx P = 1)
      (hres : ∀ x : S, σ (x : M) - (x : M) ^ p.absNorm ∈
        (algebraMap S M) '' (P : Set S)) :
      ∃ hfinite : Finite (S ⧸ P),
        letI := hP
        letI := hfinite
        σ = arithFrobAt R G P := by
    have hPne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R S)] at hmap
      exact hp hmap.symm
    letI := hP
    letI : Finite (S ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
    letI : Algebra.IsUnramifiedAt R P :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPne).mpr (by
        change (P.comap (algebraMap R S)).ramificationIdx P = 1
        rw [hmap]
        exact he)
    have hstd : IsArithFrobAt R σ P := by
      intro x
      obtain ⟨y, hy, hyval⟩ := hres x
      have hnorm : Nat.card (R ⧸ P.under R) = p.absNorm := by rw [Ideal.under, hmap]; rfl
      rw [hnorm]
      have heq : (MulSemiringAction.toAlgHom R S σ) x - x ^ p.absNorm = y := by
        apply FaithfulSMul.algebraMap_injective S M
        rw [map_sub, map_pow]
        exact (congrArg (fun z : M => z - (x : M) ^ p.absNorm)
          (algebraMap_galRestrict_apply R σ x)).trans hyval.symm
      exact heq.symm ▸ hy
    have hcanon := IsArithFrobAt.arithFrobAt R G P
    have heq := hstd.eq_of_isUnramifiedAt hcanon P.primeCompl_le_nonZeroDivisors
    refine ⟨inferInstance, ?_⟩
    apply (galRestrict R F M S).injective
    apply DFunLike.ext
    intro x
    exact DFunLike.congr_fun heq x
  have hmemone := hone
  obtain ⟨_, _, P₀, hP₀, hmap₀, he₀, hres₀⟩ := hone
  obtain ⟨hfinite₀, hcanon₀⟩ := compare 1 P₀ hP₀ hmap₀ he₀ hres₀
  letI := hP₀
  letI := hfinite₀
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmemone, ?_⟩
  intro σ hσ
  obtain ⟨_, _, P, hP, hmap, he, hres⟩ := hσ
  obtain ⟨hfinite, hcanon⟩ := compare σ P hP hmap he hres
  letI := hP
  letI := hfinite
  have hconj := isConj_arithFrobAt R G P P₀ (hmap.trans hmap₀.symm)
  rw [← hcanon, ← hcanon₀] at hconj
  exact isConj_one_left.mp hconj

lemma base_equiv_of_bottom (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω]
    (E : IntermediateField F Ω) (hE : E = ⊥) : Nonempty (F ≃ₐ[F] E) :=
  ⟨(IntermediateField.botEquiv F Ω).symm.trans (IntermediateField.equivOfEq hE.symm)⟩



end Formalization.Result.helpers.Proposition_3p8.Machinery
