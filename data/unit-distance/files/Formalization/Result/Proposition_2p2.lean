import Formalization.Result.helpers.Proposition_2p2.Machinery
import Formalization.Axioms

noncomputable section
open scoped NumberField
namespace UnitDistance

/-- Proposition 2.2, PDF-derived transcription, pp. 6–7. -/
theorem paper_2_2 (A : AdmissibleDatum) (H : ℝ) (hH : 0 < H)
    (hh : (classNumber A.K : ℝ) ≤ H ^ Module.finrank ℚ A.L) :
    ∃ U : Finset A.K,
      (∀ u ∈ U, IsIntegral ℤ ((admissibleDenominator A : A.K) * u)) ∧
      (∀ u ∈ U, u * A.c u = 1) ∧
      (∀ u ∈ U, ∀ σ : A.K →+* ℂ, ‖σ u‖ = 1) ∧
      Real.exp (translationGrowth A.t H * Module.finrank ℚ A.L) ≤ (U.card : ℝ) := (by
  -- HumanLean:proof_begin
  exact (open Formalization.Result.helpers.Proposition_2p2.Machinery in by
    classical
    let f := Module.finrank ℚ A.L
    let m := A.t * f
    let R := 𝓞 A.K
    let F := FractionalIdeal (nonZeroDivisors R) A.K
    let V := IsDedekindDomain.HeightOneSpectrum R
    let cR := NumberField.RingOfIntegers.mapRingEquiv A.c.toRingEquiv
    let τ : V → V := fun p =>
      ⟨p.asIdeal.map cR, inferInstance,
        (Ideal.map_eq_bot_iff_of_injective cR.injective).not.mpr p.ne_bot⟩
    have hτ : Function.Involutive τ := by
      intro p
      apply IsDedekindDomain.HeightOneSpectrum.ext
      change (p.asIdeal.map cR.toRingHom).map cR.toRingHom = p.asIdeal
      rw [Ideal.map_map]
      have hcR : cR.toRingHom.comp cR.toRingHom = RingHom.id R := by
        ext x
        exact conjugation_involutive A (x : A.K)
      rw [hcR, Ideal.map_id]
    let v : V → A.K → ℤ := fun p x =>
      FractionalIdeal.count A.K p (FractionalIdeal.spanSingleton (nonZeroDivisors R) x)
    -- Automorphisms transport the prime valuations of principal ideals.
    have htransport : ∀ p x, v p (A.c x) = v (τ p) x := by
      intro p x
      exact principal_count_map A.c.toRingEquiv (τ p) p
        (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (hτ p)) x
    -- Complete splitting gives tf disjoint conjugate pairs, each with v_P(Q)=1.
    have hsplit : ∀ b, completelySplit ℚ A.K (Ideal.span {(A.q b : 𝓞 ℚ)}) := by
      intro b
      apply (discriminantAndSplittingFacts.2.2.2.2 ℚ A.L A.K _).mpr
      refine ⟨A.q_split b, ?_⟩
      intro p hp hcomap
      have hqp : (A.q b : 𝓞 A.L) ∈ p := by
        have hmem : (A.q b : 𝓞 ℚ) ∈ p.comap (algebraMap (𝓞 ℚ) (𝓞 A.L)) := by
          rw [hcomap]
          exact Ideal.subset_span (Set.mem_singleton _)
        simpa only [Ideal.mem_comap, map_natCast] using hmem
      have hp0 : p ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hqp
        exact (Nat.cast_ne_zero.mpr (A.q_prime b).ne_zero) hqp
      exact split_above_admissible_prime A b p hp0 hp hqp
    obtain ⟨P, hP, hconj, hsupp⟩ : ∃ P : Fin m × Bool → V,
        Function.Injective P ∧
        (∀ s b, τ (P (s, b)) = P (s, !b)) ∧
        (∀ p, p ∈ Set.range P ↔ ∃ b, (A.q b : R) ∈ p.asIdeal) := by
      let W := fun b : Fin A.t => {p : V // (A.q b : R) ∈ p.asIdeal}
      have hW : ∀ b, Nat.card (W b) = 2 * f := by
        intro b
        exact (split_prime_card (A.q b) (A.q_prime b).ne_zero (hsplit b)).trans
          (idealArithmeticFacts.2 A.L A.K A.realL A.i A.i_sq A.generated A.c A.c_ne_one).2.1
      letI : ∀ b, Finite (W b) := fun b => Nat.finite_of_card_ne_zero (by
        rw [hW]
        exact Nat.mul_ne_zero (by decide) (Module.finrank_pos.ne'))
      letI : ∀ b, Fintype (W b) := fun b => Fintype.ofFinite (W b)
      let X := (b : Fin A.t) × W b
      let j : X → V := fun x => x.2.val
      have hj : Function.Injective j := by
        rintro ⟨b, p⟩ ⟨d, q⟩ h
        change p.val = q.val at h
        have hd : (A.q d : R) ∈ p.val.asIdeal := by rw [h]; exact q.property
        have hbd : b = d := A.q_distinct (rational_prime_below_unique p.val.asIdeal
          _ _ (A.q_prime b) (A.q_prime d) p.property hd)
        subst d
        have hpq : p = q := Subtype.ext h
        cases hpq
        rfl
      have hτmem : ∀ b (p : V), (A.q b : R) ∈ p.asIdeal → (A.q b : R) ∈ (τ p).asIdeal := by
        intro b p hp
        change (A.q b : R) ∈ p.asIdeal.map cR
        simpa [R] using (Ideal.mem_map_of_mem cR hp)
      let τX : X → X := fun x => ⟨x.1, ⟨τ x.2.val, hτmem x.1 x.2.val x.2.property⟩⟩
      have hτX : Function.Involutive τX := by
        intro x
        apply hj
        exact hτ (j x)
      have hfree : ∀ x, τX x ≠ x := by
        intro x hx
        exact conjugate_prime_ne A x.1 x.2.val x.2.property
          (congrArg (fun z => (j z).asIdeal) hx)
      have hcard : Fintype.card X = m * 2 := by
        change Fintype.card ((b : Fin A.t) × W b) = _
        rw [Fintype.card_sigma]
        have hWF : ∀ b, Fintype.card (W b) = 2 * f := by
          intro b
          simpa only [Nat.card_eq_fintype_card] using hW b
        simp only [hWF, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        dsimp only [m]
        ring
      obtain ⟨e, he⟩ := involution_pairs τX hτX hfree m hcard
      refine ⟨fun z => j (e z), hj.comp e.injective, ?_, ?_⟩
      · intro s b
        exact congrArg j (he s b)
      · intro p
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨(e z).1, (e z).2.property⟩
        · rintro ⟨b, hb⟩
          obtain ⟨z, hz⟩ := e.surjective ⟨b, ⟨p, hb⟩⟩
          exact ⟨z, congrArg j hz⟩
    have hQ : ∀ p, v p (admissiblePrimeProduct A : A.K) =
        if p ∈ Set.range P then 1 else 0 := by
      intro p
      simp only [hsupp]
      exact admissible_product_count A hsplit p
    -- The binary ideals occupy h(K) ideal classes. Choose a largest-enough fiber.
    let I : (Fin m → Bool) → Fˣ := fun ε =>
      Units.mk0 (∏ s, ((P (s, ε s)).asIdeal : F))
        (prime_product_nonzero (fun s => P (s, ε s)))
    obtain ⟨S, hSne, hSclass, hScard⟩ := large_fiber (fun ε => ClassGroup.mk (I ε))
    obtain ⟨η, hη⟩ := hSne
    have hgenerators : ∀ ε : S, ∃ x : A.Kˣ,
        (I ε : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (x : A.K) *
          (I η : F) := by
      intro ε
      exact ((idealArithmeticFacts.1 A.K).1 (I ε) (I η)).2.2.mp
        (hSclass ε ε.property η hη)
    choose α hα using hgenerators
    let u : S → A.K := fun ε => (α ε : A.K) / A.c (α ε : A.K)
    have hvα : ∀ ε p, v p (α ε : A.K) = idealValuation p (I ε) - idealValuation p (I η) := by
      intro ε p
      exact principal_generator_count (I ε) (I η) (α ε) (hα ε) p
    have hvu : ∀ ε p, v p (u ε) =
        (idealValuation p (I ε) - idealValuation p (I η)) -
        (idealValuation (τ p) (I ε) - idealValuation (τ p) (I η)) := by
      intro ε p
      change v p ((α ε : A.K) / A.c (α ε : A.K)) = _
      rw [show v p ((α ε : A.K) / A.c (α ε : A.K)) =
          v p (α ε : A.K) - v p (A.c (α ε : A.K)) from
        principal_quotient_count _ _ (Units.ne_zero _) ((map_ne_zero A.c).mpr (Units.ne_zero _)) p]
      rw [htransport, hvα, hvα]
    have hIcount : ∀ ε s b, idealValuation (P (s, b)) (I ε) =
        if ε s = b then 1 else 0 := by
      intro ε s b
      exact binary_product_count P hP ε s b
    -- The two exponents are 2(ε_s-η_s) and its negative.
    have hpair : ∀ ε s b, v (P (s, b)) (u ε) =
        2 * ((if ε.val s = b then 1 else 0) - (if η s = b then 1 else 0)) := by
      intro ε s b
      rw [hvu, hconj, hIcount, hIcount, hIcount, hIcount]
      cases hε : ε.val s <;> cases hηs : η s <;> cases b <;> simp
    have hIoutside : ∀ ε p, p ∉ Set.range P → idealValuation p (I ε) = 0 := by
      intro ε p hp
      exact binary_product_count_outside P ε p hp
    have houtside : ∀ ε p, p ∉ Set.range P → v p (u ε) = 0 := by
      intro ε p hp
      have hτp : τ p ∉ Set.range P := by
        rintro ⟨⟨s, b⟩, he⟩
        apply hp
        refine ⟨(s, !b), ?_⟩
        rw [← hconj, he, hτ p]
      rw [hvu, hIoutside _ _ hp, hIoutside _ _ hp,
        hIoutside _ _ hτp, hIoutside _ _ hτp]
      norm_num
    have hQpos : 0 < admissiblePrimeProduct A :=
      Finset.prod_pos fun b _ => (A.q_prime b).pos
    have hQnz : (admissiblePrimeProduct A : A.K) ≠ 0 := by
      exact_mod_cast hQpos.ne'
    have hunz : ∀ ε, u ε ≠ 0 := fun ε =>
      div_ne_zero (Units.ne_zero _) ((map_ne_zero A.c).mpr (Units.ne_zero _))
    -- Multiplying by Q² removes all negative finite valuations.
    have hint : ∀ ε, IsIntegral ℤ ((admissibleDenominator A : A.K) * u ε) := by
      intro ε
      apply integral_of_principal_counts_nonnegative _ (mul_ne_zero (by
        simpa only [admissibleDenominator, Nat.cast_pow] using pow_ne_zero 2 hQnz) (hunz ε))
      intro p
      change v p ((admissibleDenominator A : A.K) * u ε) ≥ 0
      have hmul : v p ((admissibleDenominator A : A.K) * u ε) =
          2 * v p (admissiblePrimeProduct A : A.K) + v p (u ε) := by
        dsimp only [v]
        rw [admissibleDenominator, Nat.cast_pow,
          ← FractionalIdeal.spanSingleton_mul_spanSingleton,
          FractionalIdeal.count_mul A.K p
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (pow_ne_zero 2 hQnz))
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hunz ε)),
          ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
        norm_num <;> rfl
      rw [hmul, hQ]
      by_cases hp : p ∈ Set.range P
      · rw [if_pos hp]
        obtain ⟨⟨s, b⟩, rfl⟩ := hp
        rw [hpair]
        split_ifs <;> norm_num
      · rw [if_neg hp, houtside ε p hp]
        norm_num
    -- Distinct binary choices have different displayed prime valuations.
    have huinj : Function.Injective u := by
      intro ε δ he
      apply Subtype.ext
      funext s
      have hv := congrArg (v (P (s, true))) he
      rw [hpair, hpair] at hv
      cases hε : ε.val s <;> cases hδ : δ.val s <;> cases hηs : η s <;>
        norm_num [hε, hδ, hηs] at hv <;> rfl
    let U := Finset.univ.image u
    refine ⟨U, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨ε, _, rfl⟩ := Finset.mem_image.mp hx
      exact hint ε
    · intro x hx
      obtain ⟨ε, _, rfl⟩ := Finset.mem_image.mp hx
      exact conjugate_quotient_norm A _ (Units.ne_zero (α ε))
    · intro x hx σ
      obtain ⟨ε, _, rfl⟩ := Finset.mem_image.mp hx
      exact conjugate_quotient_absolute_value A _ (Units.ne_zero (α ε)) σ
    · have hUcard : U.card = S.card := by
        rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_coe]
      rw [hUcard]
      have hcount : (2 : ℝ) ^ m / classNumber A.K ≤ S.card := by
        simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat, classNumber, NumberField.classNumber] using hScard
      exact (exponential_count A.t f (classNumber A.K) H hH
        (NumberField.classNumber_pos A.K) hh).trans hcount)
  -- HumanLean:proof_end
)
end UnitDistance
