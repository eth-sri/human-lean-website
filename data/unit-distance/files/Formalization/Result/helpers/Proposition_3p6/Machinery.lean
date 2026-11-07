import Formalization.Axioms
import Formalization.Definition
import Mathlib

namespace Formalization.Result.helpers.Proposition_3p6.Machinery



lemma finite_adjoin_range_root (E L : Type) [Field E] [NumberField E]
    [Field L] [Algebra ℚ L] (f : E →ₐ[ℚ] L) (i : L) (hi : i ^ 2 = -1) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range f ∪ {i})) := by
  have hf : FiniteDimensional ℚ f.fieldRange :=
    FiniteDimensional.of_injective (AlgEquiv.ofInjective f f.injective).symm.toLinearMap
      (AlgEquiv.ofInjective f f.injective).symm.injective
  have hi' : IsIntegral ℚ i := IsIntegral.of_pow (by norm_num : 0 < 2)
    (by rw [hi]; exact isIntegral_one.neg)
  haveI := IntermediateField.adjoin.finiteDimensional hi'
  rw [IntermediateField.adjoin_union]
  have hr : IntermediateField.adjoin ℚ (Set.range f) = f.fieldRange := by
    apply le_antisymm
    · exact IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
    · rintro x ⟨y, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩
  rw [hr]
  infer_instance

lemma rational_prime_norm (q : ℕ) :
    (Ideal.span {(q : NumberField.RingOfIntegers ℚ)}).absNorm = q := by
  rw [Ideal.absNorm_span_singleton]
  have h := Algebra.norm_algebraMap_of_basis
    (Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers ℚ)) (q : ℤ)
  simp only [map_natCast] at h
  rw [h]
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers ℚ)) = 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ
      (NumberField.RingOfIntegers ℚ)), NumberField.RingOfIntegers.rank]
    simp
  simp [hc]

lemma root_frobenius_congruence {R : Type*} [CommRing R] [IsDomain R]
    (a : R) (ha : a ^ 2 = -1) (h2 : (2 : R) ≠ 0)
    (q : ℕ) (hq : a ^ q = a) : q % 4 = 1 := by
  have h4 : a ^ 4 = 1 := by calc
    a ^ 4 = (a ^ 2) ^ 2 := by ring
    _ = 1 := by rw [ha]; ring
  rw [pow_eq_pow_mod q h4] at hq
  have hm := Nat.mod_lt q (by norm_num : 0 < 4)
  interval_cases h : q % 4
  · rw [pow_zero] at hq
    apply False.elim
    apply h2
    rw [← hq] at ha
    linear_combination ha
  · rfl
  · rw [ha] at hq
    apply False.elim
    apply h2
    rw [← hq] at ha
    linear_combination ha
  · rw [show a ^ 3 = a ^ 2 * a by ring, ha, neg_one_mul] at hq
    have hz : (2 : R) * a = 0 := by linear_combination -hq
    have ha0 := (mul_eq_zero.mp hz).resolve_left h2
    simp [ha0] at ha

lemma split_prime_congruence (K : Type) [Field K] [NumberField K]
    [IsGalois ℚ K] (i : K) (hi : i ^ 2 = -1)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hs : UnitDistance.completelySplit ℚ K
      (Ideal.span {(q : NumberField.RingOfIntegers ℚ)})) : q % 4 = 1 := by
  let p : Ideal (NumberField.RingOfIntegers ℚ) := Ideal.span {(q : NumberField.RingOfIntegers ℚ)}
  have hf := (UnitDistance.discriminantAndSplittingFacts.2.2.2.1 ℚ K p).mp hs
  have hm : (1 : K ≃ₐ[ℚ] K) ∈ UnitDistance.frobeniusClass ℚ K p := by rw [hf]; simp
  obtain ⟨_, _, P, hP, hcomap, _, hpow⟩ := hm
  letI := hP
  have hint : IsIntegral ℤ i := IsIntegral.of_pow (by norm_num : 0 < 2)
    (by rw [hi]; exact isIntegral_one.neg)
  let j : NumberField.RingOfIntegers K := ⟨i, hint⟩
  have hj : j ^ 2 = -1 := by apply Subtype.ext; exact hi
  let a := Ideal.Quotient.mk P j
  have ha : a ^ 2 = -1 := by
    change (Ideal.Quotient.mk P j) ^ 2 = -1
    rw [← map_pow, hj, map_neg, map_one]
  have haF : a ^ q = a := by
    obtain ⟨z, hz, heq⟩ := hpow j
    have heq' : z = j - j ^ q := by
      apply NumberField.RingOfIntegers.coe_injective
      rw [show p.absNorm = q from rational_prime_norm q] at heq
      simpa only [map_sub, map_pow, AlgEquiv.one_apply] using heq
    have hmj : j - j ^ q ∈ P := heq' ▸ hz
    have hh := (Ideal.Quotient.eq_zero_iff_mem).mpr hmj
    have hh' : a - a ^ q = 0 := by simpa only [map_sub, map_pow] using hh
    exact (sub_eq_zero.mp hh').symm
  have h2 : (2 : NumberField.RingOfIntegers K ⧸ P) ≠ 0 := by
    intro hzero
    have hmem : (2 : NumberField.RingOfIntegers K) ∈ P := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using hzero
    have hbase : (2 : NumberField.RingOfIntegers ℚ) ∈ p := by
      rw [← hcomap]
      simpa only [Ideal.mem_comap, map_ofNat] using hmem
    have hdiv := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hbase)
    have hdiv' : q ∣ 2 := by
      change (Ideal.span {(q : NumberField.RingOfIntegers ℚ)}).absNorm ∣
        (Ideal.span {(2 : NumberField.RingOfIntegers ℚ)}).absNorm at hdiv
      rw [rational_prime_norm q] at hdiv
      have hn2 : (Ideal.span {(2 : NumberField.RingOfIntegers ℚ)}).absNorm = 2 := by
        simpa only [Nat.cast_ofNat] using rational_prime_norm 2
      rw [hn2] at hdiv
      exact hdiv
    exact hq2 ((Nat.dvd_prime Nat.prime_two).mp hdiv' |>.resolve_left hq.ne_one)
  exact root_frobenius_congruence a ha h2 q haF



end Formalization.Result.helpers.Proposition_3p6.Machinery
