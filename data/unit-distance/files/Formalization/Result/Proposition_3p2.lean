import Formalization.Result.helpers.Proposition_3p2.Machinery
import Formalization.Axioms

noncomputable section
open scoped NumberField
namespace UnitDistance
attribute [local instance 2000] CyclotomicField.algebra

/-- Proposition 3.2. All subfields are formed in the common cyclotomic field.
The degree product states joint linear disjointness of this finite family. -/
theorem paper_3_2 (A : CubicCharacterDatum) :
    let m := ∏ j, A.r j
    letI : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun j _ => (A.r_prime j).ne_zero)⟩
    let ψ : Fin A.ell → DirichletCharacter ℂ m := fun j =>
      DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) (A.χ j)
    let L := fun j => characterFixedField {ψ j}
    let M := ⨆ j, L j
    let F := characterFixedField {∏ j, ψ j}
    (∀ j, totallyReal (L j) ∧ Module.finrank ℚ (L j) = 3 ∧ IsGalois ℚ (L j)) ∧
    Module.finrank ℚ M = ∏ j, Module.finrank ℚ (L j) ∧
    IsGalois ℚ M ∧ Nonempty ((M ≃ₐ[ℚ] M) ≃* (Fin A.ell → Multiplicative (ZMod 3))) ∧
    totallyReal F ∧ Module.finrank ℚ F = 3 ∧ IsGalois ℚ F ∧
    Nonempty ((F ≃ₐ[ℚ] F) ≃* Multiplicative (ZMod 3)) ∧
    absoluteDiscriminant F = m ^ 2 ∧
    ∃ hFM : F ≤ M,
      letI : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
      IsGalois F M ∧
      Nonempty ((M ≃ₐ[F] M) ≃* (Fin (A.ell - 1) → Multiplicative (ZMod 3))) ∧
      everywhereUnramified F M := (by
  -- HumanLean:proof_begin
  classical
  intro m ψ L M F
  letI : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun j _ => (A.r_prime j).ne_zero)⟩
  have horder : ∀ j, orderOf (ψ j) = 3 := by
    intro j
    exact (orderOf_injective _ (DirichletCharacter.changeLevel_injective _) _).trans
      (A.cubic j)
  have hL : ∀ j, totallyReal (L j) ∧ Module.finrank ℚ (L j) = 3 ∧ IsGalois ℚ (L j) := by
    intro j
    letI := Formalization.Result.helpers.Proposition_3p2.Machinery.cyclotomic_subfield_isGalois
      (L j)
    have hd : Module.finrank ℚ (L j) = 3 :=
      (Formalization.Result.helpers.Proposition_3p2.Machinery.singleton_finrank
        (ψ j)).trans (horder j)
    exact ⟨Formalization.Result.helpers.Proposition_3p2.Machinery.totallyReal_of_odd_galois_degree
      (L j) (hd.symm ▸ (show Odd 3 by decide)), hd, inferInstance⟩
  have hFM : F ≤ M :=
    Formalization.Result.helpers.Proposition_3p2.Machinery.product_fixedField_le_compositum ψ
  have hGM : IsGalois ℚ M :=
    Formalization.Result.helpers.Proposition_3p2.Machinery.cyclotomic_subfield_isGalois M
  have hGF : IsGalois ℚ F :=
    Formalization.Result.helpers.Proposition_3p2.Machinery.cyclotomic_subfield_isGalois F
  letI : ∀ j, NeZero (A.r j) := fun j => ⟨(A.r_prime j).ne_zero⟩
  have hcop : Pairwise (fun i j => Nat.Coprime (A.r i) (A.r j)) := by
    intro i j hij
    exact (Nat.coprime_primes (A.r_prime i) (A.r_prime j)).mpr
      (fun h => hij (A.r_distinct h))
  -- The product character and its square retain every prime conductor.
  have hc : characterConductor (∏ j, ψ j) = m :=
    Formalization.Result.helpers.Proposition_3p2.Machinery.conductor_prod_inflated
      A.r A.χ (fun j => Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) hcop A.primitive _
  have hc₂ : characterConductor ((∏ j, ψ j) ^ 2) = m := by
    have h := Formalization.Result.helpers.Proposition_3p2.Machinery.conductor_prod_inflated
      A.r (fun j => A.χ j ^ 2) (fun j => Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) hcop
      (fun j => Formalization.Result.helpers.Proposition_3p2.Machinery.cubic_square_conductor
        (A.r_prime j) (A.χ j) (A.cubic j)) Finset.univ
    simpa only [map_pow, Finset.prod_pow] using h
  have hm : m ≠ 1 := by
    intro he
    have hd : A.r ⟨0, A.ell_pos⟩ ∣ m := Finset.dvd_prod_of_mem A.r (Finset.mem_univ _)
    rw [he, Nat.dvd_one] at hd
    exact (A.r_prime _).ne_one hd
  have hprodorder : orderOf (∏ j, ψ j) = 3 := by
    apply orderOf_eq_prime
    · rw [← Finset.prod_pow]
      exact Finset.prod_eq_one (fun j _ => (horder j) ▸ pow_orderOf_eq_one (ψ j))
    · intro he
      rw [he] at hc
      exact hm (hc.symm.trans (DirichletCharacter.conductor_one (NeZero.ne m)))
  have hdegF : Module.finrank ℚ F = 3 :=
    (Formalization.Result.helpers.Proposition_3p2.Machinery.singleton_finrank
      (∏ j, ψ j)).trans hprodorder
  have hrealF : totallyReal F := by
    letI := hGF
    exact Formalization.Result.helpers.Proposition_3p2.Machinery.totallyReal_of_odd_galois_degree
      F (hdegF.symm ▸ (show Odd 3 by decide))
  have hdiscF : absoluteDiscriminant F = m ^ 2 := by
    have h := Formalization.Result.helpers.Proposition_3p2.Machinery.cyclic_cubic_discriminant
      (∏ j, ψ j) hprodorder
    rw [hc, hc₂, ← pow_two] at h
    exact h
  -- Coprime conductors give independent character coordinates.
  let P := ∀ j, Subgroup.zpowers (A.χ j)
  let f (j : Fin A.ell) : Subgroup.zpowers (A.χ j) →* DirichletCharacter ℂ m :=
    (DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem A.r (Finset.mem_univ j))).comp
      (Subgroup.zpowers (A.χ j)).subtype
  let φ : P →* DirichletCharacter ℂ m :=
    { toFun := fun a => ∏ j, f j (a j)
      map_one' := by change (∏ j, f j 1) = 1; simp
      map_mul' := by
        intro a b
        change (∏ j, f j (a j * b j)) = (∏ j, f j (a j)) * (∏ j, f j (b j))
        simp only [map_mul, Finset.prod_mul_distrib] }
  have hinj : Function.Injective φ := by
    apply (injective_iff_map_eq_one φ).mpr
    intro a ha
    have h := (Formalization.Result.helpers.Proposition_3p2.Machinery.inflated_product_eq_one_iff
      A.r (fun j => (a j).val) (fun j => Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) hcop).mp ha
    funext j
    exact Subtype.ext (h j)
  have hrange : φ.range = Subgroup.closure (Set.range ψ) := by
    apply Formalization.Result.helpers.Proposition_3p2.Machinery.product_cyclic_range
      (fun j => Subgroup.zpowers (A.χ j)) (fun j => ⟨A.χ j, Subgroup.mem_zpowers _⟩)
      ?_ f φ (fun _ => rfl)
    intro j x
    rcases x.property with ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩
  have hMX : characterFixedField (φ.range : Set (DirichletCharacter ℂ m)) = M := by
    rw [hrange, Formalization.Result.helpers.Proposition_3p2.Machinery.characterFixedField_closure]
    exact Formalization.Result.helpers.Proposition_3p2.Machinery.characterFixedField_range ψ
  let eP : P ≃* (Fin A.ell → Multiplicative (ZMod 3)) := MulEquiv.piCongrRight
    (fun j => mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, A.cubic j]
      simp))
  have hGalP : Nonempty ((M ≃ₐ[ℚ] M) ≃* P) := by
    rw [← hMX]
    exact ⟨(Formalization.Result.helpers.Proposition_3p2.Machinery.subgroup_aut_equiv_characters
      φ.range).some.trans (MulEquiv.ofBijective φ.rangeRestrict
        ⟨fun _ _ h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).symm⟩
  let eM := hGalP.some.trans eP
  have hdegM : Module.finrank ℚ M = 3 ^ A.ell := by
    letI := hGM
    exact (IsGalois.card_aut_eq_finrank ℚ M).symm.trans
      (by simpa using Nat.card_congr eM.toEquiv)
  have hdisjoint : Module.finrank ℚ M = ∏ j, Module.finrank ℚ (L j) := by
    simpa only [funext (fun j => (hL j).2.1), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hdegM
  -- In each coordinate, two of the three exponents retain its prime conductor.
  letI : Fintype φ.range := Fintype.ofFinite _
  letI : ∀ j, Fintype (Subgroup.zpowers (A.χ j)) := fun j => Fintype.ofFinite _
  let eX : P ≃ φ.range := Equiv.ofBijective φ.rangeRestrict
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  let eA : (Fin A.ell → ZMod 3) ≃ P := Equiv.piCongrRight (fun j =>
    (finCongr (A.cubic j).symm).trans (finEquivZPowers (isOfFinOrder_of_finite (A.χ j))))
  have hdiscM : absoluteDiscriminant M = m ^ (2 * 3 ^ (A.ell - 1)) := by
    have hD := cyclotomicCharacterFacts.2.2.1 m φ.range
    rw [hMX] at hD
    calc
      absoluteDiscriminant M = ∏ χ : φ.range, characterConductor χ.val := hD
      _ = ∏ a : P, characterConductor (φ a) := (eX.prod_comp _).symm
      _ = ∏ a : Fin A.ell → ZMod 3, characterConductor (φ (eA a)) := (eA.prod_comp _).symm
      _ = ∏ a : Fin A.ell → ZMod 3, ∏ j, if a j = 0 then 1 else A.r j := by
        apply Finset.prod_congr rfl
        intro a _
        have hcA := Formalization.Result.helpers.Proposition_3p2.Machinery.conductor_prod_coprime_levels
          A.r (fun j => A.χ j ^ (a j).val)
          (fun j => Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) hcop Finset.univ
        change characterConductor (∏ j, DirichletCharacter.changeLevel
          (Finset.dvd_prod_of_mem A.r (Finset.mem_univ j)) (A.χ j ^ (a j).val)) = _
        rw [hcA]
        apply Finset.prod_congr rfl
        intro j _
        exact Formalization.Result.helpers.Proposition_3p2.Machinery.cubic_power_conductor
          (A.r_prime j) (A.χ j) (A.cubic j) (a j)
      _ = _ := Formalization.Result.helpers.Proposition_3p2.Machinery.product_coordinate_supports A.r
  have hrealM : totallyReal M := by
    letI := hGM
    exact Formalization.Result.helpers.Proposition_3p2.Machinery.totallyReal_of_odd_galois_degree
      M (hdegM.symm ▸ (show Odd (3 ^ A.ell) from (by decide : Odd 3).pow))
  refine ⟨hL, hdisjoint, hGM, ⟨eM⟩, hrealF, hdegF, hGF,
    Formalization.Result.helpers.Proposition_3p2.Machinery.singleton_cubic_aut
      (∏ j, ψ j) hprodorder, hdiscF, ?_⟩
  refine ⟨hFM, ?_⟩
  letI algFM : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  letI : Module F M := @Algebra.toModule F M _ _ algFM
  letI : Module ℚ F := Algebra.toModule
  letI : Module ℚ M := Algebra.toModule
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq (fun q => by simp)
  letI := hGM
  letI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  have hrel : Module.finrank F M = 3 ^ (A.ell - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3)
    calc
      3 * Module.finrank F M = Module.finrank ℚ F * Module.finrank F M :=
        congrArg (· * Module.finrank F M) hdegF.symm
      _ = Module.finrank ℚ M := Module.finrank_mul_finrank ℚ F M
      _ = 3 ^ A.ell := hdegM
      _ = 3 * 3 ^ (A.ell - 1) := by
        conv_lhs => rw [show A.ell = (A.ell - 1) + 1 by have := A.ell_pos; omega]
        rw [pow_succ, mul_comm]
  -- The relative group is a subgroup of the elementary abelian cubic group.
  have hrelGal : Nonempty ((M ≃ₐ[F] M) ≃* (Fin (A.ell - 1) → Multiplicative (ZMod 3))) :=
    Formalization.Result.helpers.Proposition_3p2.Machinery.relative_aut_equiv
      F M A.ell (A.ell - 1) eM hrel
  refine ⟨inferInstance, hrelGal, ?_⟩
  -- Equality in the tower formula forces discriminant norm one.
  have hdiscpow : absoluteDiscriminant M = absoluteDiscriminant F ^ Module.finrank F M := by
    calc
      absoluteDiscriminant M = m ^ (2 * 3 ^ (A.ell - 1)) := hdiscM
      _ = (m ^ 2) ^ (3 ^ (A.ell - 1)) := pow_mul _ _ _
      _ = absoluteDiscriminant F ^ Module.finrank F M :=
        congrArg₂ (fun x n : ℕ => x ^ n) hdiscF.symm hrel.symm
  exact Formalization.Result.helpers.Proposition_3p2.Machinery.unramified_of_discriminant_norm_one
    F M (Formalization.Result.helpers.Proposition_3p2.Machinery.norm_relativeDiscriminant_eq_one
      F M hdiscpow) hrealM
  -- HumanLean:proof_end
)
end UnitDistance
