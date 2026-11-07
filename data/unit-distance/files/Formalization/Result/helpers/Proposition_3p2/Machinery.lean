import Formalization.Axioms
import Formalization.Definition
import Mathlib

namespace Formalization.Result.helpers.Proposition_3p2.Machinery



lemma conductor_changeLevel {n m : ℕ} [NeZero n] [NeZero m]
    (h : n ∣ m) (χ : DirichletCharacter ℂ n) :
    UnitDistance.characterConductor (DirichletCharacter.changeLevel h χ) =
      UnitDistance.characterConductor χ := by
  let ψ := DirichletCharacter.changeLevel h χ
  apply Nat.dvd_antisymm
  · exact ψ.conductor_dvd_of_mem_conductorSet (NeZero.ne m)
      ⟨dvd_trans χ.conductor_dvd_level h, χ.primitiveCharacter, by
        simpa only [← DirichletCharacter.changeLevel_trans] using
          (congrArg (DirichletCharacter.changeLevel h)
            χ.changeLevel_primitiveCharacter).symm⟩
  · have he : DirichletCharacter.changeLevel (Nat.dvd_mul_right n ψ.conductor) χ =
        DirichletCharacter.changeLevel (Nat.dvd_mul_left ψ.conductor n)
          ψ.primitiveCharacter := by
      apply DirichletCharacter.changeLevel_injective
        (Nat.mul_dvd_mul_left n ψ.conductor_dvd_level)
      have hx := congrArg (DirichletCharacter.changeLevel (Nat.dvd_mul_left m n))
        ψ.changeLevel_primitiveCharacter
      simpa only [ψ, ← DirichletCharacter.changeLevel_trans] using hx.symm
    have hd := DirichletCharacter.factorsThrough_gcd χ ψ.primitiveCharacter he
    exact dvd_trans
      (χ.conductor_dvd_of_mem_conductorSet (NeZero.ne n) hd)
      (Nat.gcd_dvd_right _ _)

lemma prime_conductor_of_ne_one {r : ℕ} (hr : r.Prime)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    UnitDistance.characterConductor χ = r := by
  rcases (Nat.dvd_prime hr).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ ((χ.eq_one_iff_conductor_eq_one hr.ne_zero).mpr h))
  · exact h

lemma cubic_square_conductor {r : ℕ} (hr : r.Prime)
    (χ : DirichletCharacter ℂ r) (hχ : orderOf χ = 3) :
    UnitDistance.characterConductor (χ ^ 2) = r := by
  apply prime_conductor_of_ne_one hr
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  norm_num at hd

lemma norm_relativeDiscriminant_eq_one
    (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M]
    (hD : UnitDistance.absoluteDiscriminant M =
      UnitDistance.absoluteDiscriminant F ^ Module.finrank F M) :
    (UnitDistance.relativeDiscriminant F M).absNorm = 1 := by
  have ht := (UnitDistance.discriminantAndSplittingFacts.1 F M).1
  have hn : UnitDistance.absoluteDiscriminant F ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)
  have hp := pow_ne_zero (Module.finrank F M) hn
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp)
  simpa only [mul_one] using ht.symm.trans hD

lemma unramified_of_discriminant_norm_one
    (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M]
    (hn : (UnitDistance.relativeDiscriminant F M).absNorm = 1)
    (hreal : UnitDistance.totallyReal M) : UnitDistance.everywhereUnramified F M := by
  have hd := (UnitDistance.discriminantAndSplittingFacts.2.1 F _).mp hn
  exact ⟨(UnitDistance.discriminantAndSplittingFacts.1 F M).2.mp hd,
    fun σ _ x => hreal σ x⟩

lemma character_kernel_closed {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    letI := CyclotomicField.algebra m ℚ
    Subgroup.closure
      {σ : (CyclotomicField m ℚ) ≃ₐ[ℚ] (CyclotomicField m ℚ) |
        χ ((IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
          (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)) σ :
            (ZMod m)ˣ) : ZMod m) = 1} =
      (χ.toUnitHom.comp (IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
        (CyclotomicField m ℚ)
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))).toMonoidHom).ker := by
  letI := CyclotomicField.algebra m ℚ
  let e := IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
    (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hs : {σ | χ ((e σ : (ZMod m)ˣ) : ZMod m) = 1} =
      ((χ.toUnitHom.comp e.toMonoidHom).ker : Set _) := by
    ext σ
    change χ ((e σ : (ZMod m)ˣ) : ZMod m) = 1 ↔ χ.toUnitHom (e σ) = 1
    exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
  rw [hs, Subgroup.closure_eq]

lemma fixingSubgroup_character_singleton {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    letI := CyclotomicField.algebra m ℚ
    (UnitDistance.characterFixedField {χ}).fixingSubgroup =
      (χ.toUnitHom.comp (IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
        (CyclotomicField m ℚ)
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))).toMonoidHom).ker := by
  letI := CyclotomicField.algebra m ℚ
  unfold UnitDistance.characterFixedField
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [IntermediateField.fixingSubgroup_fixedField, character_kernel_closed]

lemma product_fixedField_le_compositum {ι : Type} [Fintype ι]
    {m : ℕ} [NeZero m] (χ : ι → DirichletCharacter ℂ m) :
    letI := CyclotomicField.algebra m ℚ
    UnitDistance.characterFixedField {∏ j, χ j} ≤
      ⨆ j, UnitDistance.characterFixedField {χ j} := by
  letI := CyclotomicField.algebra m ℚ
  letI := IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  let M := ⨆ j, UnitDistance.characterFixedField {χ j}
  change UnitDistance.characterFixedField {∏ j, χ j} ≤ M
  rw [← IsGalois.fixedField_fixingSubgroup M]
  conv_lhs => rw [← IsGalois.fixedField_fixingSubgroup
    (UnitDistance.characterFixedField {∏ j, χ j})]
  apply IntermediateField.fixedField_le
  intro σ hσ
  rw [fixingSubgroup_character_singleton]
  have hj : ∀ j, σ ∈ (UnitDistance.characterFixedField {χ j}).fixingSubgroup :=
    fun j => IntermediateField.fixingSubgroup_le (le_iSup (fun j =>
      UnitDistance.characterFixedField {χ j}) j) hσ
  simp only [fixingSubgroup_character_singleton, MonoidHom.mem_ker,
    MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe] at hj ⊢
  change MulChar.mulEquivToUnitHom (∏ j, χ j) _ = 1
  rw [map_prod, MonoidHom.finset_prod_apply]
  exact Finset.prod_eq_one (fun j _ => hj j)

lemma count_nonzero_coordinate {n : ℕ} (j : Fin n) :
    (Finset.univ.filter (fun a : Fin n → ZMod 3 => a j ≠ 0)).card =
      2 * 3 ^ (n - 1) := by
  classical
  have hz : (Finset.univ.filter (fun a : Fin n → ZMod 3 => a j = 0)).card =
      3 ^ (n - 1) := by
    simpa using Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset (ZMod 3)) j (Finset.mem_univ (0 : ZMod 3))
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → ZMod 3))) (p := fun a => a j = 0)
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hp : 3 ^ n = 3 * 3 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, hz, hp] at hsum
  change 3 ^ (n - 1) + (Finset.univ.filter
    (fun a : Fin n → ZMod 3 => a j ≠ 0)).card = 3 * 3 ^ (n - 1) at hsum
  omega

lemma product_coordinate_supports {n : ℕ} (r : Fin n → ℕ) :
    (∏ a : Fin n → ZMod 3, ∏ j : Fin n, if a j = 0 then 1 else r j) =
      (∏ j, r j) ^ (2 * 3 ^ (n - 1)) := by
  classical
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = ∏ a ∈ Finset.univ.filter (fun a : Fin n → ZMod 3 => a j ≠ 0), r j := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      by_cases h : a j = 0 <;> simp [h]
    _ = _ := by rw [Finset.prod_const, count_nonzero_coordinate]

lemma cyclotomic_subfield_isGalois {m : ℕ} [NeZero m] :
    letI := CyclotomicField.algebra m ℚ
    ∀ E : IntermediateField ℚ (CyclotomicField m ℚ), IsGalois ℚ E := by
  letI := CyclotomicField.algebra m ℚ
  letI := IsCyclotomicExtension.isAbelianGalois {m} ℚ (CyclotomicField m ℚ)
  intro E
  exact (IsAbelianGalois.of_algHom E.val).toIsGalois

lemma singleton_aut_equiv_character_range {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    letI := CyclotomicField.algebra m ℚ
    let L := UnitDistance.characterFixedField {χ}
    Nonempty ((L ≃ₐ[ℚ] L) ≃* χ.toUnitHom.range) := by
  letI := CyclotomicField.algebra m ℚ
  letI := IsCyclotomicExtension.isAbelianGalois {m} ℚ (CyclotomicField m ℚ)
  let e := IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
    (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  let φ := χ.toUnitHom.comp e.toMonoidHom
  have hL : UnitDistance.characterFixedField {χ} = IntermediateField.fixedField φ.ker := by
    unfold UnitDistance.characterFixedField
    simp only [Set.mem_singleton_iff, forall_eq, character_kernel_closed]
    rfl
  change Nonempty (((UnitDistance.characterFixedField {χ}) ≃ₐ[ℚ]
    (UnitDistance.characterFixedField {χ})) ≃* χ.toUnitHom.range)
  rw [hL]
  have hr : φ.range = χ.toUnitHom.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp [φ]⟩
  exact ⟨(IsGalois.normalAutEquivQuotient φ.ker).symm.trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hr))⟩

lemma character_range_card {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Nat.card χ.toUnitHom.range = orderOf χ := by
  classical
  apply Nat.dvd_antisymm
  · rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val,
      Units.val_one, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe,
      pow_orderOf_eq_one, MulChar.one_apply_coe]
  · apply orderOf_dvd_of_pow_eq_one
    apply MulChar.ext
    intro x
    have hx := congrArg (fun y : χ.toUnitHom.range => ((y : ℂˣ) : ℂ))
      (pow_card_eq_one' (x := χ.toUnitHom.rangeRestrict x))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val,
      Units.val_one, MonoidHom.coe_rangeRestrict, MulChar.coe_toUnitHom,
      MulChar.pow_apply_coe, MulChar.one_apply_coe] using hx

lemma singleton_finrank {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Module.finrank ℚ (UnitDistance.characterFixedField {χ}) = orderOf χ := by
  letI := CyclotomicField.algebra m ℚ
  letI := cyclotomic_subfield_isGalois (UnitDistance.characterFixedField {χ})
  obtain ⟨e⟩ := singleton_aut_equiv_character_range χ
  rw [← IsGalois.card_aut_eq_finrank,
    Nat.card_congr e.toEquiv, character_range_card]

lemma singleton_cubic_aut {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hχ : orderOf χ = 3) :
    Nonempty (((UnitDistance.characterFixedField {χ}) ≃ₐ[ℚ]
      (UnitDistance.characterFixedField {χ})) ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨e⟩ := singleton_aut_equiv_character_range χ
  exact ⟨e.trans (mulEquivOfCyclicCardEq (by
    rw [character_range_card, hχ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]))⟩

lemma totallyReal_of_odd_galois_degree (K : Type) [Field K] [NumberField K]
    [IsGalois ℚ K] (h : Odd (Module.finrank ℚ K)) : UnitDistance.totallyReal K := by
  letI := IsUnramifiedAtInfinitePlaces_of_odd_finrank (k := ℚ) h
  intro σ x
  have hu := NumberField.InfinitePlace.isUnramified ℚ (NumberField.InfinitePlace.mk σ)
  have hr := (NumberField.InfinitePlace.isUnramified_iff.mp hu).resolve_right
    (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr
      (NumberField.IsTotallyReal.isReal _))
  have he := NumberField.InfinitePlace.isReal_mk_iff.mp hr
  exact Complex.conj_eq_iff_im.mp (congrArg (fun f : K →+* ℂ => f x)
    (NumberField.ComplexEmbedding.isReal_iff.mp he))

lemma conductor_mul_inflated {a b m : ℕ} [NeZero a] [NeZero b] [NeZero m]
    (ha : a ∣ m) (hb : b ∣ m) (hab : Nat.Coprime a b)
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b)
    (hχ : UnitDistance.characterConductor χ = a)
    (hψ : UnitDistance.characterConductor ψ = b) :
    UnitDistance.characterConductor
      (DirichletCharacter.changeLevel ha χ * DirichletCharacter.changeLevel hb ψ) = a * b := by
  letI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hd : a * b ∣ m := hab.mul_dvd_of_dvd_of_dvd ha hb
  let θ := DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ *
    DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ
  have he : DirichletCharacter.changeLevel hd θ =
      DirichletCharacter.changeLevel ha χ * DirichletCharacter.changeLevel hb ψ := by
    simp only [θ, map_mul, ← DirichletCharacter.changeLevel_trans]
  rw [← he, conductor_changeLevel]
  exact UnitDistance.cyclotomicCharacterFacts.2.2.2 a b hab χ ψ hχ hψ

lemma conductor_prod_inflated {ι : Type} {m : ℕ} [NeZero m]
    (r : ι → ℕ) [∀ j, NeZero (r j)] (χ : ∀ j, DirichletCharacter ℂ (r j))
    (hd : ∀ j, r j ∣ m)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j)))
    (hp : ∀ j, UnitDistance.characterConductor (χ j) = r j)
    (s : Finset ι) :
    UnitDistance.characterConductor (∏ j ∈ s, DirichletCharacter.changeLevel (hd j) (χ j)) =
      ∏ j ∈ s, r j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UnitDistance.characterConductor, DirichletCharacter.conductor_one (NeZero.ne m)]
  | @insert j s hj ih =>
    let ψ := ∏ i ∈ s, DirichletCharacter.changeLevel (hd i) (χ i)
    letI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero (NeZero.ne m)⟩
    have hcop : Nat.Coprime (r j) ψ.conductor := by
      change Nat.Coprime (r j) (UnitDistance.characterConductor ψ)
      rw [ih]
      exact Nat.Coprime.prod_right (fun i hi => hc (by rintro rfl; exact hj hi))
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    change UnitDistance.characterConductor (DirichletCharacter.changeLevel (hd j) (χ j) * ψ) = _
    calc
      _ = UnitDistance.characterConductor (DirichletCharacter.changeLevel (hd j) (χ j) *
          DirichletCharacter.changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter) := by
        rw [DirichletCharacter.changeLevel_primitiveCharacter]
      _ = r j * ψ.conductor := conductor_mul_inflated _ _ hcop _ _ (hp j)
        ψ.primitiveCharacter_isPrimitive
      _ = _ := congrArg (r j * ·) ih

lemma characterFixedField_zpowers {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    UnitDistance.characterFixedField (Subgroup.zpowers χ : Set (DirichletCharacter ℂ m)) =
      UnitDistance.characterFixedField {χ} := by
  letI := CyclotomicField.algebra m ℚ
  unfold UnitDistance.characterFixedField
  apply congrArg IntermediateField.fixedField
  apply congrArg Subgroup.closure
  ext σ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  let u := IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
    (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)) σ
  let ev : DirichletCharacter ℂ m →* ℂˣ :=
    (MonoidHom.eval u).comp MulChar.mulEquivToUnitHom.toMonoidHom
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h η hη
    have hχ : χ ∈ ev.ker := Units.ext h
    have he := (Subgroup.zpowers_le.mpr hχ) hη
    exact congrArg Units.val he

lemma cyclic_cubic_discriminant {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : orderOf χ = 3) :
    UnitDistance.absoluteDiscriminant (UnitDistance.characterFixedField {χ}) =
      UnitDistance.characterConductor χ * UnitDistance.characterConductor (χ ^ 2) := by
  classical
  letI : Fintype (Subgroup.zpowers χ) := Fintype.ofFinite _
  have hd := UnitDistance.cyclotomicCharacterFacts.2.2.1 m (Subgroup.zpowers χ)
  rw [characterFixedField_zpowers] at hd
  rw [hd]
  let e := (finCongr hχ.symm).trans (finEquivZPowers (isOfFinOrder_of_finite χ))
  rw [← e.prod_comp]
  change (∏ i : Fin 3, UnitDistance.characterConductor (χ ^ (i : ℕ))) = _
  simp [Fin.prod_univ_succ, UnitDistance.characterConductor,
    DirichletCharacter.conductor_one (NeZero.ne m)]

lemma character_evaluation_surjective {m : ℕ} [NeZero m]
    (X : Subgroup (DirichletCharacter ℂ m)) :
    Function.Surjective (fun u : (ZMod m)ˣ =>
      (MonoidHom.eval u).comp (MulChar.mulEquivToUnitHom.toMonoidHom.comp X.subtype)) := by
  intro η
  obtain ⟨η', hη'⟩ := MonoidHom.restrict_surjective ℂ X η
  let ζ := η'.comp MulChar.mulEquivToUnitHom.symm.toMonoidHom
  refine ⟨CommGroup.monoidHomMonoidHomEquiv (ZMod m)ˣ ℂ ζ, ?_⟩
  apply MonoidHom.ext
  intro χ
  change χ.val.toUnitHom (CommGroup.monoidHomMonoidHomEquiv (ZMod m)ˣ ℂ ζ) = η χ
  rw [CommGroup.apply_monoidHomMonoidHomEquiv]
  have he := DFunLike.congr_fun hη' χ
  simpa [ζ] using he

lemma subgroup_aut_equiv_characters {m : ℕ} [NeZero m]
    (X : Subgroup (DirichletCharacter ℂ m)) :
    Nonempty (((UnitDistance.characterFixedField (X : Set (DirichletCharacter ℂ m))) ≃ₐ[ℚ]
      (UnitDistance.characterFixedField (X : Set (DirichletCharacter ℂ m)))) ≃* X) := by
  classical
  letI := CyclotomicField.algebra m ℚ
  letI := IsCyclotomicExtension.isAbelianGalois {m} ℚ (CyclotomicField m ℚ)
  let e := IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
    (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  let ev : (ZMod m)ˣ →* (X →* ℂˣ) :=
    { toFun := fun u => (MonoidHom.eval u).comp
        (MulChar.mulEquivToUnitHom.toMonoidHom.comp X.subtype)
      map_one' := by ext χ; simp
      map_mul' := by intros; ext χ; simp }
  let φ := ev.comp e.toMonoidHom
  have hs : Function.Surjective φ :=
    (character_evaluation_surjective X).comp e.surjective
  have hF : UnitDistance.characterFixedField (X : Set (DirichletCharacter ℂ m)) =
      IntermediateField.fixedField φ.ker := by
    unfold UnitDistance.characterFixedField
    apply congrArg IntermediateField.fixedField
    have hset : {σ | ∀ χ ∈ X, χ ((e σ : (ZMod m)ˣ) : ZMod m) = 1} =
        (φ.ker : Set _) := by
      ext σ
      change (∀ χ ∈ X, χ ((e σ : (ZMod m)ˣ) : ZMod m) = 1) ↔ φ σ = 1
      constructor
      · intro h
        apply MonoidHom.ext
        intro χ
        exact Units.ext (h χ.val χ.property)
      · intro h χ hχ
        exact congrArg Units.val (DFunLike.congr_fun h ⟨χ, hχ⟩)
    change Subgroup.closure {σ | ∀ χ ∈ X, χ ((e σ : (ZMod m)ˣ) : ZMod m) = 1} = φ.ker
    rw [hset, Subgroup.closure_eq]
  rw [hF]
  exact ⟨(IsGalois.normalAutEquivQuotient φ.ker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hs).trans
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity X ℂ).some)⟩

lemma conductor_prod_coprime_levels {ι : Type} {m : ℕ} [NeZero m]
    (r : ι → ℕ) [∀ j, NeZero (r j)] (χ : ∀ j, DirichletCharacter ℂ (r j))
    (hd : ∀ j, r j ∣ m)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (s : Finset ι) :
    UnitDistance.characterConductor (∏ j ∈ s, DirichletCharacter.changeLevel (hd j) (χ j)) =
      ∏ j ∈ s, UnitDistance.characterConductor (χ j) := by
  letI : ∀ j, NeZero (χ j).conductor := fun j =>
    ⟨(χ j).conductor_ne_zero (NeZero.ne (r j))⟩
  have h := conductor_prod_inflated (fun j => (χ j).conductor)
    (fun j => (χ j).primitiveCharacter)
    (fun j => dvd_trans (χ j).conductor_dvd_level (hd j))
    (fun i j hij => Nat.Coprime.of_dvd (χ i).conductor_dvd_level
      (χ j).conductor_dvd_level (hc hij))
    (fun j => (χ j).primitiveCharacter_isPrimitive) s
  have he (j : ι) : DirichletCharacter.changeLevel
      (dvd_trans (χ j).conductor_dvd_level (hd j)) (χ j).primitiveCharacter =
        DirichletCharacter.changeLevel (hd j) (χ j) := by
    simpa only [← DirichletCharacter.changeLevel_trans] using
      congrArg (DirichletCharacter.changeLevel (hd j)) (χ j).changeLevel_primitiveCharacter
  simpa only [he] using h

lemma inflated_product_eq_one_iff {ι : Type} [Fintype ι] {m : ℕ} [NeZero m]
    (r : ι → ℕ) [∀ j, NeZero (r j)] (χ : ∀ j, DirichletCharacter ℂ (r j))
    (hd : ∀ j, r j ∣ m)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) :
    (∏ j, DirichletCharacter.changeLevel (hd j) (χ j)) = 1 ↔ ∀ j, χ j = 1 := by
  classical
  constructor
  · intro h j
    have hp := conductor_prod_coprime_levels r χ hd hc Finset.univ
    rw [h] at hp
    have hdj : UnitDistance.characterConductor (χ j) ∣ 1 := by
      rw [← DirichletCharacter.conductor_one (R := ℂ) (NeZero.ne m)]
      rw [show (1 : DirichletCharacter ℂ m).conductor =
        ∏ j, UnitDistance.characterConductor (χ j) from hp]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    exact ((χ j).eq_one_iff_conductor_eq_one (NeZero.ne (r j))).mpr
      (Nat.dvd_one.mp hdj)
  · intro h
    simp [h]

lemma characterFixedField_closure {m : ℕ} [NeZero m]
    (S : Set (DirichletCharacter ℂ m)) :
    UnitDistance.characterFixedField (Subgroup.closure S : Set (DirichletCharacter ℂ m)) =
      UnitDistance.characterFixedField S := by
  letI := CyclotomicField.algebra m ℚ
  unfold UnitDistance.characterFixedField
  apply congrArg IntermediateField.fixedField
  apply congrArg Subgroup.closure
  ext σ
  let u := IsCyclotomicExtension.autEquivPow (n := m) (K := ℚ)
    (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)) σ
  let ev : DirichletCharacter ℂ m →* ℂˣ :=
    (MonoidHom.eval u).comp MulChar.mulEquivToUnitHom.toMonoidHom
  change (∀ χ ∈ Subgroup.closure S, χ (u : ZMod m) = 1) ↔ ∀ χ ∈ S, χ (u : ZMod m) = 1
  constructor
  · intro h χ hχ
    exact h χ (Subgroup.subset_closure hχ)
  · intro h χ hχ
    have hs : Subgroup.closure S ≤ ev.ker := (Subgroup.closure_le _).mpr
      (fun η hη => Units.ext (h η hη))
    exact congrArg Units.val (hs hχ)

lemma characterFixedField_range {ι : Type} {m : ℕ} [NeZero m]
    (χ : ι → DirichletCharacter ℂ m) :
    letI := CyclotomicField.algebra m ℚ
    UnitDistance.characterFixedField (Set.range χ) =
      ⨆ j, UnitDistance.characterFixedField {χ j} := by
  letI := CyclotomicField.algebra m ℚ
  letI := IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  let M := ⨆ j, UnitDistance.characterFixedField {χ j}
  change UnitDistance.characterFixedField (Set.range χ) = M
  apply le_antisymm
  · conv_rhs => rw [← IsGalois.fixedField_fixingSubgroup M]
    apply IntermediateField.fixedField_le
    intro σ hσ
    apply Subgroup.subset_closure
    rintro η ⟨j, rfl⟩
    have hj := IntermediateField.fixingSubgroup_le
      (le_iSup (fun j => UnitDistance.characterFixedField {χ j}) j) hσ
    rw [fixingSubgroup_character_singleton] at hj
    exact congrArg Units.val hj
  · apply iSup_le
    intro j
    apply IntermediateField.fixedField_le
    apply Subgroup.closure_mono
    intro σ hσ η hη
    rcases Set.mem_singleton_iff.mp hη with rfl
    exact hσ _ (Set.mem_range_self j)

lemma product_cyclic_range {ι : Type} [Fintype ι] {G : Type} [CommGroup G]
    (H : ι → Type) [∀ j, Group (H j)] (g : ∀ j, H j)
    (hg : ∀ j x, x ∈ Subgroup.zpowers (g j)) (f : ∀ j, H j →* G)
    (φ : (∀ j, H j) →* G) (hφ : ∀ x, φ x = ∏ j, f j (x j)) :
    φ.range = Subgroup.closure (Set.range (fun j => f j (g j))) := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [hφ]
    apply Subgroup.prod_mem
    intro j _
    have hj : f j (x j) ∈ Subgroup.zpowers (f j (g j)) := by
      rcases hg j (x j) with ⟨z, hz⟩
      change g j ^ z = x j at hz
      exact ⟨z, by change f j (g j) ^ z = f j (x j); rw [← map_zpow, hz]⟩
    exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_range_self j))) hj
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨j, rfl⟩
    refine ⟨Pi.mulSingle j (g j), ?_⟩
    rw [hφ, Finset.prod_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.mulSingle_eq_of_ne hij]
    · simp

lemma exponent_three_group_equiv (G : Type) [CommGroup G] [Finite G]
    (n : ℕ) (hp : ∀ g : G, g ^ 3 = 1) (hc : Nat.card G = 3 ^ n) :
    Nonempty (G ≃* (Fin n → Multiplicative (ZMod 3))) := by
  letI : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule
    (fun g => congrArg Additive.ofMul (hp g.toMul))
  let b := Module.finBasis (ZMod 3) (Additive G)
  have he : 3 ^ Module.finrank (ZMod 3) (Additive G) = 3 ^ n := by
    have h := Nat.card_congr b.equivFun.toEquiv
    simpa using h.symm.trans hc
  have hn : Module.finrank (ZMod 3) (Additive G) = n :=
    Nat.pow_right_injective (by decide : 1 < 3) he
  let e := (Module.finBasisOfFinrankEq (ZMod 3) (Additive G) hn).equivFun.toAddEquiv
  exact ⟨e.toMultiplicative.trans (MulEquiv.piMultiplicative (fun _ : Fin n => ZMod 3))⟩

lemma cubic_power_conductor {r : ℕ} (hr : r.Prime)
    (χ : DirichletCharacter ℂ r) (hχ : orderOf χ = 3) (a : ZMod 3) :
    UnitDistance.characterConductor (χ ^ a.val) = if a = 0 then 1 else r := by
  have hne : χ ≠ 1 := by intro h; simp [h] at hχ
  have h₁ := prime_conductor_of_ne_one hr χ hne
  have h₂ := cubic_square_conductor hr χ hχ
  fin_cases a
  · change UnitDistance.characterConductor (χ ^ 0) = 1
    exact (congrArg UnitDistance.characterConductor (pow_zero χ)).trans
      (DirichletCharacter.conductor_one hr.ne_zero)
  · change UnitDistance.characterConductor (χ ^ 1) = r
    simpa only [pow_one] using h₁
  · change UnitDistance.characterConductor (χ ^ 2) = r
    exact h₂

lemma relative_aut_equiv (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M] [IsScalarTower ℚ F M]
    [IsGalois F M] (n k : ℕ)
    (e : (M ≃ₐ[ℚ] M) ≃* (Fin n → Multiplicative (ZMod 3)))
    (hd : Module.finrank F M = 3 ^ k) :
    Nonempty ((M ≃ₐ[F] M) ≃* (Fin k → Multiplicative (ZMod 3))) := by
  let ρ : (M ≃ₐ[F] M) →* (Fin n → Multiplicative (ZMod 3)) :=
    { toFun := fun σ => e (σ.restrictScalars ℚ)
      map_one' := by change e 1 = 1; exact map_one e
      map_mul' := by
        intro σ τ
        change e (σ.restrictScalars ℚ * τ.restrictScalars ℚ) = _
        exact map_mul e _ _ }
  have hinj : Function.Injective ρ := fun _ _ h =>
    AlgEquiv.restrictScalars_injective ℚ (e.injective h)
  letI := MonoidHom.commGroupOfInjective ρ hinj
  apply exponent_three_group_equiv _ k
  · intro σ
    apply hinj
    rw [map_pow, map_one]
    funext j
    exact (show ∀ z : Multiplicative (ZMod 3), z ^ 3 = 1 from
      fun z => by simpa using (pow_card_eq_one' (x := z))) _
  · exact (IsGalois.card_aut_eq_finrank F M).trans hd



end Formalization.Result.helpers.Proposition_3p2.Machinery
