import Formalization.Axioms
import Formalization.Definition
import Mathlib

namespace Formalization.Result.helpers.Proposition_2p2.Machinery



lemma conjugation_involutive (A : UnitDistance.AdmissibleDatum) :
    Function.Involutive A.c := by
  have hc := (UnitDistance.idealArithmeticFacts.2 A.L A.K A.realL A.i
    A.i_sq A.generated A.c A.c_ne_one).2.2
  let σ : A.K →+* ℂ := Classical.choice inferInstance
  intro x
  apply σ.injective
  rw [hc, hc, star_star]

lemma conjugate_quotient_norm (A : UnitDistance.AdmissibleDatum)
    (x : A.K) (hx : x ≠ 0) :
    (x / A.c x) * A.c (x / A.c x) = 1 := by
  have hcx : A.c x ≠ 0 := (map_ne_zero A.c).mpr hx
  rw [map_div₀, conjugation_involutive A x]
  field_simp

lemma conjugate_quotient_absolute_value (A : UnitDistance.AdmissibleDatum)
    (x : A.K) (hx : x ≠ 0) (σ : A.K →+* ℂ) :
    ‖σ (x / A.c x)‖ = 1 := by
  have hc := (UnitDistance.idealArithmeticFacts.2 A.L A.K A.realL A.i
    A.i_sq A.generated A.c A.c_ne_one).2.2
  rw [map_div₀, hc, norm_div, norm_star]
  exact div_self (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))

lemma large_fiber {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (g : X → Y) :
    ∃ S : Finset X, S.Nonempty ∧
      (∀ x ∈ S, ∀ y ∈ S, g x = g y) ∧
      (Fintype.card X : ℝ) / Fintype.card Y ≤ S.card := by
  classical
  have hy : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  obtain ⟨y, hy⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum
    (f := g) (w := fun _ => (1 : ℝ))
    (b := (Fintype.card X : ℝ) / Fintype.card Y) (by
      simp only [nsmul_eq_mul, Finset.sum_const, Finset.card_univ, mul_one]
      exact le_of_eq (mul_div_cancel₀ (Fintype.card X : ℝ) hy.ne'))
  let S := Finset.univ.filter (fun x => g x = y)
  have hs : (Fintype.card X : ℝ) / Fintype.card Y ≤ S.card := by
    simpa [S] using hy
  refine ⟨S, ?_, ?_, hs⟩
  · apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    have hypos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (div_pos hpos hypos).trans_le hs
  · intro x hx z hz
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm

lemma exponential_count (t f h : ℕ) (H : ℝ) (hH : 0 < H)
    (hhpos : 0 < h) (hh : (h : ℝ) ≤ H ^ f) :
    Real.exp (UnitDistance.translationGrowth t H * f) ≤
      (2 : ℝ) ^ (t * f) / h := by
  have heq : Real.exp (UnitDistance.translationGrowth t H * f) =
      (2 : ℝ) ^ (t * f) / H ^ f := by
    unfold UnitDistance.translationGrowth
    rw [sub_mul, Real.exp_sub]
    have hn : (t : ℝ) * Real.log 2 * f = (t * f : ℕ) * Real.log 2 := by
      push_cast
      ring
    rw [hn, mul_comm (Real.log H), Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num),
      Real.exp_log hH]
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hhpos) hh

lemma prime_product_nonzero {K : Type} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι]
    (P : ι → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∏ s, (P s).asIdeal :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun s _ =>
    FractionalIdeal.coeIdeal_ne_zero.mpr (P s).ne_bot

lemma binary_product_count {K : Type} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι]
    (P : ι × Bool → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : Function.Injective P) (ε : ι → Bool) (s : ι) (b : Bool) :
    FractionalIdeal.count K (P (s, b))
      (∏ j, (P (j, ε j)).asIdeal :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
      if ε s = b then 1 else 0 := by
  classical
  rw [FractionalIdeal.count_prod K (P (s, b)) Finset.univ _
    (fun j _ => FractionalIdeal.coeIdeal_ne_zero.mpr (P (j, ε j)).ne_bot)]
  simp only [FractionalIdeal.count_maximal, hP.eq_iff, Prod.mk.injEq]
  rw [Finset.sum_eq_single s]
  · simp
  · intro j _ hjs
    simp [hjs]
  · simp

lemma binary_product_count_outside {K : Type} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι]
    (P : ι × Bool → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ε : ι → Bool)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hp : p ∉ Set.range P) :
    FractionalIdeal.count K p
      (∏ j, (P (j, ε j)).asIdeal :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 0 := by
  classical
  rw [FractionalIdeal.count_prod K p Finset.univ _
    (fun j _ => FractionalIdeal.coeIdeal_ne_zero.mpr (P (j, ε j)).ne_bot)]
  apply Finset.sum_eq_zero
  intro j _
  exact FractionalIdeal.count_maximal_coprime K p
    (fun h => hp ⟨(j, ε j), h⟩)

lemma principal_generator_count {K : Type} [Field K] [NumberField K]
    (I J : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)
    (x : Kˣ)
    (hx : (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
      FractionalIdeal.spanSingleton _ (x : K) * (J : FractionalIdeal _ K))
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K)) =
      UnitDistance.idealValuation p I - UnitDistance.idealValuation p J := by
  have h := congrArg (FractionalIdeal.count K p) hx
  rw [FractionalIdeal.count_mul K p
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero x)) (Units.ne_zero J)] at h
  exact eq_sub_of_add_eq h.symm

lemma principal_quotient_count {K : Type} [Field K] [NumberField K]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (x / y)) =
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x) -
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) y) := by
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv]
  rw [FractionalIdeal.count_mul K p
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv, sub_eq_add_neg]

lemma integral_of_principal_counts_nonnegative {K : Type} [Field K] [NumberField K]
    (x : K) (hx : x ≠ 0)
    (hv : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      0 ≤ FractionalIdeal.count K p (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x)) : IsIntegral ℤ x := by
  let I := Units.mk0 (FractionalIdeal.spanSingleton
    (nonZeroDivisors (NumberField.RingOfIntegers K)) x)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
  have hi := ((UnitDistance.idealArithmeticFacts.1 K).2.1 I).mpr hv
  have hm := FractionalIdeal.spanSingleton_le_iff_mem.mp hi
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp hm
  rw [← hz]
  exact z.isIntegral_coe

lemma integral_ideal_count_map {K : Type} [Field K] [NumberField K]
    (e : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K)
    (p q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hpq : p.asIdeal.map e.toRingHom = q.asIdeal)
    (J : Ideal (NumberField.RingOfIntegers K)) (hJ : J ≠ ⊥) :
    FractionalIdeal.count K q (J.map e.toRingHom :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
    FractionalIdeal.count K p (J :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
  classical
  have hm : J.map e.toRingHom ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hJ
  rw [FractionalIdeal.count_coe K q hm, FractionalIdeal.count_coe K p hJ]
  congr 1
  have hn : ∀ n : ℕ,
      n ≤ (Associates.mk q.asIdeal).count (Associates.mk (J.map e.toRingHom)).factors ↔
      n ≤ (Associates.mk p.asIdeal).count (Associates.mk J).factors := by
    intro n
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hm) q.associates_irreducible,
      ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) p.associates_irreducible,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, ← hpq,
      ← Ideal.map_pow]
    constructor
    · intro h
      have hc := Ideal.comap_mono (f := e.toRingHom) h
      simpa only [Ideal.comap_map_of_bijective e.toRingHom e.bijective] using hc
    · exact Ideal.map_mono
  exact le_antisymm ((hn _).mp le_rfl) ((hn _).mpr le_rfl)

lemma principal_count_map {K : Type} [Field K] [NumberField K]
    (e : K ≃+* K)
    (p q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hpq : p.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom = q.asIdeal)
    (x : K) :
    FractionalIdeal.count K q (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (e x)) =
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) x) := by
  classical
  by_cases hx : x = 0
  · simp [hx, FractionalIdeal.count_zero]
  let R := NumberField.RingOfIntegers K
  let eR := NumberField.RingOfIntegers.mapRingEquiv e
  have hi : ∀ z : R, z ≠ 0 →
      FractionalIdeal.count K q (FractionalIdeal.spanSingleton (nonZeroDivisors R) (e (z : K))) =
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton (nonZeroDivisors R) (z : K)) := by
    intro z hz
    have h := integral_ideal_count_map eR p q hpq (Ideal.span {z})
      (Ideal.span_singleton_eq_bot.not.mpr hz)
    simpa only [Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton] using h
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : (b : K) ≠ 0 := by
    intro h
    exact hb0 ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  have haK : (a : K) ≠ 0 := by
    intro ha
    apply hx
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [ha, zero_div]
  have ha0 : a ≠ 0 := by intro ha; exact haK (congrArg (algebraMap R K) ha)
  rw [← hab]
  change FractionalIdeal.count K q (FractionalIdeal.spanSingleton (nonZeroDivisors R)
    (e ((a : K) / (b : K)))) = _
  rw [map_div₀,
    principal_quotient_count _ _ ((map_ne_zero e).mpr haK) ((map_ne_zero e).mpr hbK),
    principal_quotient_count _ _ haK hbK, hi a ha0, hi b hb0]

lemma residue_quadratic_roots {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] (q : ℕ) (hq : q.Prime) (hmod : q % 4 = 1)
    (hqp : (q : R) ∈ p) :
    (2 : R) ∉ p ∧ ∃ a b : R ⧸ p, a ≠ b ∧ a ^ 2 + 1 = 0 ∧ b ^ 2 + 1 = 0 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hqzero : (q : R ⧸ p) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hqp : Ideal.Quotient.mk p (q : R) = 0)
  letI : CharP (R ⧸ p) q := (CharP.charP_iff_prime_eq_zero hq).mpr hqzero
  have htwo : (2 : R ⧸ p) ≠ 0 := by
    intro h
    have hd : q ∣ 2 := (CharP.cast_eq_zero_iff (R ⧸ p) q 2).mp (by simpa using h)
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hge := hq.two_le
    omega
  have hp2 : (2 : R) ∉ p := by
    intro h
    apply htwo
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr h : Ideal.Quotient.mk p (2 : R) = 0)
  obtain ⟨z, hz⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mpr (by omega)
  let a : R ⧸ p := ZMod.castHom (dvd_refl q) (R ⧸ p) z
  have ha : a ^ 2 = -1 := by
    have h := congrArg (ZMod.castHom (dvd_refl q) (R ⧸ p)) hz
    simpa only [map_neg, map_one, map_mul, map_pow, ← pow_two] using h.symm
  have ha0 : a ≠ 0 := by
    intro h
    have : (0 : R ⧸ p) = -1 := by simpa [h] using ha
    exact (neg_ne_zero.mpr one_ne_zero) this.symm
  refine ⟨hp2, a, -a, ?_, by rw [ha]; simp, by rw [neg_sq, ha]; simp⟩
  intro h
  have hz : 2 * a = 0 := by
    rw [two_mul]
    calc a + a = -a + a := congrArg (fun x => x + a) h
         _ = 0 := neg_add_cancel a
  exact (mul_ne_zero htwo ha0) hz

lemma split_above_admissible_prime (A : UnitDistance.AdmissibleDatum)
    (b : Fin A.t) (p : Ideal (NumberField.RingOfIntegers A.L))
    (hp0 : p ≠ ⊥) (hp : p.IsPrime) (hqp : (A.q b : NumberField.RingOfIntegers A.L) ∈ p) :
    UnitDistance.completelySplit A.L A.K p := by
  letI := hp
  obtain ⟨h2, hroots⟩ := residue_quadratic_roots p (A.q b) (A.q_prime b) (A.q_mod_four b) hqp
  exact ((UnitDistance.discriminantAndSplittingFacts.2.2.1 A.L A.K A.realL A.i
    A.i_sq A.generated).2 p hp0 hp h2).mpr hroots

lemma split_prime_count {K : Type} [Field K] [NumberField K]
    (q : ℕ) (hsplit : UnitDistance.completelySplit ℚ K
      (Ideal.span {(q : NumberField.RingOfIntegers ℚ)}))
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [Decidable ((q : NumberField.RingOfIntegers K) ∈ p.asIdeal)] :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (q : K)) =
      if (q : NumberField.RingOfIntegers K) ∈ p.asIdeal then 1 else 0 := by
  classical
  let J : Ideal (NumberField.RingOfIntegers ℚ) := Ideal.span {(q : NumberField.RingOfIntegers ℚ)}
  let g := algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)
  have hmap : J.map g = Ideal.span {(q : NumberField.RingOfIntegers K)} := by
    simp [J, g, Ideal.map_span]
  have hmap0 : J.map g ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hsplit.1
  have hc : FractionalIdeal.count K p (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (q : K)) =
      (J.ramificationIdx p.asIdeal : ℤ) := by
    have hcoe : (J.map g : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        FractionalIdeal.spanSingleton _ (q : K) := by
      rw [hmap, FractionalIdeal.coeIdeal_span_singleton, map_natCast]
    rw [← hcoe, FractionalIdeal.count_coe K p hmap0,
      count_associates_factors_eq hmap0 p.isPrime p.ne_bot,
      Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmap0 p.isPrime p.ne_bot]
  rw [hc]
  by_cases hqp : (q : NumberField.RingOfIntegers K) ∈ p.asIdeal
  · rw [if_pos hqp]
    have hle : J ≤ p.asIdeal.comap g := by
      apply Ideal.map_le_iff_le_comap.mp
      rw [hmap]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqp)
    have hcomap : p.asIdeal.comap g = J :=
      ((hsplit.2.1.isMaximal hsplit.1).eq_of_le (Ideal.comap_ne_top g p.isPrime.ne_top) hle).symm
    rw [(hsplit.2.2.2 p.asIdeal p.isPrime hcomap).1]
    norm_num
  · rw [if_neg hqp, Ideal.ramificationIdx_of_not_le]
    · norm_num
    · rw [hmap]
      intro h
      exact hqp (h (Ideal.subset_span (Set.mem_singleton _)))

lemma rational_prime_below_unique {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] (q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hqp : (q : R) ∈ p) (hrp : (r : R) ∈ p) : q = r := by
  have hq0 : (q : R ⧸ p) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hqp : Ideal.Quotient.mk p (q : R) = 0)
  have hr0 : (r : R ⧸ p) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hrp : Ideal.Quotient.mk p (r : R) = 0)
  exact CharP.eq (R ⧸ p) ((CharP.charP_iff_prime_eq_zero hq).mpr hq0)
    ((CharP.charP_iff_prime_eq_zero hr).mpr hr0)

lemma principal_product_count {K : Type} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] (x : ι → K) (hx : ∀ i, x i ≠ 0)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (∏ i, x i)) =
      ∑ i, FractionalIdeal.count K p (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (x i)) := by
  classical
  let sp : K →* FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
    { toFun := FractionalIdeal.spanSingleton _
      map_one' := FractionalIdeal.spanSingleton_one
      map_mul' := fun _ _ => (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm }
  change FractionalIdeal.count K p (sp (∏ i, x i)) = _
  rw [map_prod]
  exact FractionalIdeal.count_prod K p Finset.univ _
    (fun i _ => FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hx i))

lemma admissible_product_count (A : UnitDistance.AdmissibleDatum)
    (hsplit : ∀ b, UnitDistance.completelySplit ℚ A.K
      (Ideal.span {(A.q b : NumberField.RingOfIntegers ℚ)}))
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers A.K))
    [Decidable (∃ b, (A.q b : NumberField.RingOfIntegers A.K) ∈ p.asIdeal)] :
    FractionalIdeal.count A.K p (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers A.K)) (UnitDistance.admissiblePrimeProduct A : A.K)) =
      if ∃ b, (A.q b : NumberField.RingOfIntegers A.K) ∈ p.asIdeal then 1 else 0 := by
  classical
  rw [UnitDistance.admissiblePrimeProduct, Nat.cast_prod, principal_product_count
    (fun b => (A.q b : A.K)) (fun b => Nat.cast_ne_zero.mpr (A.q_prime b).ne_zero)]
  simp_rw [split_prime_count _ (hsplit _)]
  split_ifs with hp
  · obtain ⟨b, hb⟩ := hp
    rw [Finset.sum_eq_single b]
    · simp [hb]
    · intro d _ hdb
      have hd : (A.q d : NumberField.RingOfIntegers A.K) ∉ p.asIdeal := by
        intro hd
        exact hdb (A.q_distinct (rational_prime_below_unique p.asIdeal _ _
          (A.q_prime d) (A.q_prime b) hd hb))
      simp [hd]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    simp only [if_neg (fun hb => hp ⟨b, hb⟩)]

lemma quadratic_automorphism_cases (A : UnitDistance.AdmissibleDatum)
    (σ : A.K ≃ₐ[A.L] A.K) : σ = 1 ∨ σ = A.c := by
  classical
  have hdim := (UnitDistance.idealArithmeticFacts.2 A.L A.K A.realL A.i
    A.i_sq A.generated A.c A.c_ne_one).1
  have hcard : Fintype.card (A.K ≃ₐ[A.L] A.K) ≤ 2 := hdim ▸ AlgEquiv.card_le
  have hs : (Finset.univ : Finset (A.K ≃ₐ[A.L] A.K)) = {1, A.c} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, Finset.card_pair A.c_ne_one.symm] using hcard
  have hmem : σ ∈ ({1, A.c} : Finset (A.K ≃ₐ[A.L] A.K)) := hs ▸ Finset.mem_univ σ
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

lemma conjugate_prime_ne (A : UnitDistance.AdmissibleDatum) (b : Fin A.t)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers A.K))
    (hqP : (A.q b : NumberField.RingOfIntegers A.K) ∈ P.asIdeal) :
    P.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv A.c.toRingEquiv).toRingHom ≠ P.asIdeal := by
  classical
  let RL := NumberField.RingOfIntegers A.L
  let RK := NumberField.RingOfIntegers A.K
  let cR := NumberField.RingOfIntegers.mapRingEquiv A.c.toRingEquiv
  let p : Ideal RL := P.asIdeal.comap (algebraMap RL RK)
  have hqp : (A.q b : RL) ∈ p := by
    change algebraMap RL RK (A.q b : RL) ∈ P.asIdeal
    simpa [RL, RK] using hqP
  have hp0 : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqp
    exact (Nat.cast_ne_zero.mpr (A.q_prime b).ne_zero) hqp
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  have hs := split_above_admissible_prime A b p hp0 hp hqp
  have hdim := (UnitDistance.idealArithmeticFacts.2 A.L A.K A.realL A.i
    A.i_sq A.generated A.c A.c_ne_one).1
  letI : Algebra.IsQuadraticExtension A.L A.K := ⟨hdim⟩
  let X := {Q : Ideal RK // Q.IsPrime ∧ Q.comap (algebraMap RL RK) = p}
  let x : X := ⟨P.asIdeal, P.isPrime, rfl⟩
  have hcard : Nat.card X = 2 := hs.2.2.1.trans hdim
  obtain ⟨y, hxy, _⟩ := (Nat.card_eq_two_iff' x).mp hcard
  have hPm : P.asIdeal ∈ Ideal.primesOver p RK := by
    refine ⟨P.isPrime, ?_⟩
    exact ⟨rfl⟩
  have hym : y.val ∈ Ideal.primesOver p RK := by
    refine ⟨y.property.1, ?_⟩
    exact ⟨y.property.2.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq RL A.L A.K RK hPm hym
  intro hfixed
  have hfix_comap : P.asIdeal.comap cR.toRingHom = P.asIdeal := by
    calc
      P.asIdeal.comap cR.toRingHom = (P.asIdeal.map cR.toRingHom).comap cR.toRingHom := by rw [hfixed]
      _ = P.asIdeal := Ideal.comap_map_of_bijective cR.toRingHom cR.bijective
  have hrestrict : (galRestrict RL A.L A.K RK A.c).toRingHom = cR.toRingHom := by
    apply RingHom.ext
    intro z
    apply NumberField.RingOfIntegers.ext
    exact algebraMap_galRestrict_apply RL A.c z
  apply hxy
  apply Subtype.ext
  change y.val = P.asIdeal
  rcases quadratic_automorphism_cases A σ with rfl | rfl
  · simpa using hσ.symm
  · have hc : P.asIdeal.comap (galRestrict RL A.L A.K RK A.c).toRingHom = y.val := hσ
    rw [hrestrict, hfix_comap] at hc
    exact hc.symm

lemma involution_pairs {X : Type*} [Fintype X] (τ : X → X)
    (hτ : Function.Involutive τ) (hfree : ∀ x, τ x ≠ x)
    (n : ℕ) (hcard : Fintype.card X = n * 2) :
    ∃ e : (Fin n × Bool) ≃ X, ∀ s b, τ (e (s, b)) = e (s, !b) := by
  classical
  let k := Fintype.equivFin X
  let Y := {x : X // k x < k (τ x)}
  let g : Y × Bool → X := fun z => if z.2 then τ z.1.val else z.1.val
  have hinj : Function.Injective g := by
    rintro ⟨x, a⟩ ⟨y, b⟩ h
    cases a <;> cases b
    · exact Prod.ext (Subtype.ext h) rfl
    · change x.val = τ y.val at h
      have hx := x.property
      rw [h, hτ] at hx
      exact False.elim ((not_lt_of_gt y.property) hx)
    · change τ x.val = y.val at h
      have hy := y.property
      rw [← h, hτ] at hy
      exact False.elim ((not_lt_of_gt x.property) hy)
    · exact Prod.ext (Subtype.ext (hτ.injective h)) rfl
  have hsurj : Function.Surjective g := by
    intro x
    by_cases hx : k x < k (τ x)
    · exact ⟨(⟨x, hx⟩, false), rfl⟩
    · have hne : k (τ x) ≠ k x := fun h => hfree x (k.injective h)
      have ht : k (τ x) < k (τ (τ x)) := by
        rw [hτ]
        exact lt_of_le_of_ne (le_of_not_gt hx) hne
      exact ⟨(⟨τ x, ht⟩, true), hτ x⟩
  let E : (Y × Bool) ≃ X := Equiv.ofBijective g ⟨hinj, hsurj⟩
  have hY : Fintype.card Y = n := by
    have h := Fintype.card_congr E
    rw [Fintype.card_prod, Fintype.card_bool] at h
    omega
  let d : Fin n ≃ Y := (Fintype.equivFinOfCardEq hY).symm
  refine ⟨(Equiv.prodCongr d (Equiv.refl Bool)).trans E, ?_⟩
  intro s b
  cases b
  · rfl
  · exact hτ (d s).val

lemma split_prime_card {K : Type} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (hsplit : UnitDistance.completelySplit ℚ K
      (Ideal.span {(q : NumberField.RingOfIntegers ℚ)})) :
    Nat.card {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (q : NumberField.RingOfIntegers K) ∈ p.asIdeal} = Module.finrank ℚ K := by
  let R := NumberField.RingOfIntegers K
  let g := algebraMap (NumberField.RingOfIntegers ℚ) R
  let J : Ideal (NumberField.RingOfIntegers ℚ) := Ideal.span {(q : NumberField.RingOfIntegers ℚ)}
  let X := {p : IsDedekindDomain.HeightOneSpectrum R // (q : R) ∈ p.asIdeal}
  let Y := {p : Ideal R // p.IsPrime ∧ p.comap g = J}
  have hcomap : ∀ P : IsDedekindDomain.HeightOneSpectrum R,
      (q : R) ∈ P.asIdeal → P.asIdeal.comap g = J := by
    intro P hp
    apply ((hsplit.2.1.isMaximal hsplit.1).eq_of_le
      (Ideal.comap_ne_top g P.isPrime.ne_top) ?_).symm
    apply Ideal.span_le.mpr
    rintro z rfl
    change g (q : NumberField.RingOfIntegers ℚ) ∈ P.asIdeal
    simpa only [map_natCast] using hp
  have hmem : ∀ P : Y, (q : R) ∈ P.val := by
    intro P
    have h : (q : NumberField.RingOfIntegers ℚ) ∈ P.val.comap g := by
      rw [P.property.2]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [Ideal.mem_comap, map_natCast] using h
  have hne : ∀ P : Y, P.val ≠ ⊥ := by
    intro P h
    have hm := hmem P
    rw [h, Ideal.mem_bot] at hm
    exact (Nat.cast_ne_zero.mpr hq) hm
  let e : X ≃ Y :=
    { toFun := fun P => ⟨P.val.asIdeal, P.val.isPrime, hcomap P.val P.property⟩
      invFun := fun P => ⟨⟨P.val, P.property.1, hne P⟩, hmem P⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans hsplit.2.2.1



end Formalization.Result.helpers.Proposition_2p2.Machinery
