import Formalization.Result.helpers.Proposition_3p6.Machinery
import Formalization.Axioms

noncomputable section
open scoped NumberField
namespace UnitDistance

/-- Proposition 3.6. Compatible Frobenius means a representative whose
restriction is Frobenius in every finite Galois subextension. -/
theorem paper_3_6 (F : Type) [Field F] [NumberField F]
    (hreal : totallyReal F) (hcubic : Module.finrank ℚ F = 3)
    (i : AlgebraicClosure F) (hi : i ^ 2 = -1)
    (t : ℕ) (ht : 0 < t) (S : Finset ℕ) :
    let Ω := maximalUnramifiedProPExtension F 3 Nat.prime_three
    let G := Ω ≃ₐ[F] Ω
    let E := IntermediateField.fixedField (frattiniSubgroup G)
    let T := IntermediateField.adjoin ℚ
      (Set.range (fun x : E => ((x : Ω) : AlgebraicClosure F)) ∪ {i})
    let N := IntermediateField.normalClosure ℚ T (AlgebraicClosure F)
    ∃ hE : NumberField E,
      letI := hE
      ∃ hEGal : IsGalois F E,
        letI := hEGal
        ∃ hN : NumberField N,
          letI := hN
          ∃ q : Fin t → ℕ, Function.Injective q ∧
            ∀ b, (q b).Prime ∧ q b ∉ S ∧
              completelySplit ℚ N (Ideal.span {(q b : 𝓞 ℚ)}) ∧
              q b % 4 = 1 ∧ completelySplit ℚ F (Ideal.span {(q b : 𝓞 ℚ)}) ∧
              ∀ p : Ideal (𝓞 F), p ≠ ⊥ → p.IsPrime →
                p.comap (algebraMap (𝓞 ℚ) (𝓞 F)) = Ideal.span {(q b : 𝓞 ℚ)} →
                frobeniusClass F E p = {1} ∧
                ∃ σ : G, σ ∈ frattiniSubgroup G ∧
                  ∀ J : IntermediateField F Ω, ∀ hJ : NumberField J,
                    letI := hJ
                    ∀ hJGal : IsGalois F J,
                      letI := hJGal
                      AlgEquiv.restrictNormal σ J ∈ frobeniusClass F J p := (by
  -- HumanLean:proof_begin
  classical
  let Ω := maximalUnramifiedProPExtension F 3 Nat.prime_three
  let G := Ω ≃ₐ[F] Ω
  let E := IntermediateField.fixedField (frattiniSubgroup G)
  let T := IntermediateField.adjoin ℚ
    (Set.range (fun x : E => ((x : Ω) : AlgebraicClosure F)) ∪ {i})
  let N := IntermediateField.normalClosure ℚ T (AlgebraicClosure F)
  obtain ⟨hΩ, hfg, hpro, hemb, hunram, hfixed, hfrob⟩ :=
    unramifiedClassFieldCorrespondence F
  letI := hΩ
  -- Class field theory and the Frattini theorem make E/F finite Galois.
  obtain ⟨hΦ, hopen, d, hd, hequiv⟩ :=
    (frattiniQuotientFacts 3 Nat.prime_three
      (InfiniteGalois.profiniteGalGrp F Ω) hpro hfg).2.1
  obtain ⟨hE, hEGal, hdeg, hfix⟩ := hfixed (frattiniSubgroup G) hΦ hopen
  letI := hE
  letI := hEGal
  refine ⟨hE, hEGal, ?_⟩
  -- Adjoin i and take the finite normal closure over the rationals.
  let f : E →ₐ[ℚ] AlgebraicClosure F :=
    (Ω.val.restrictScalars ℚ).comp (E.val.restrictScalars ℚ)
  haveI : FiniteDimensional ℚ T :=
    Formalization.Result.helpers.Proposition_3p6.Machinery.finite_adjoin_range_root
      E (AlgebraicClosure F) f i hi
  haveI : NumberField N := { to_finiteDimensional := inferInstance }
  refine ⟨inferInstance, ?_⟩
  -- Chebotarev supplies arbitrarily many distinct split primes, excluding 2.
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) :=
    ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)⟩
  haveI : IsGalois ℚ (AlgebraicClosure F) := {}
  haveI : IsGalois ℚ N := IsGalois.normalClosure ℚ T (AlgebraicClosure F)
  have hprimes := chebotarevSplitPrimes N (insert 2 S)
  let primes := hprimes.natEmbedding _
  let q : Fin t → ℕ := fun b => (primes b.val).val
  have hq : Function.Injective q := by
    intro b c h
    apply Fin.ext
    exact primes.injective (Subtype.ext h)
  -- Splitting descends from N to E and then to F.
  have hEN (x : E) : f x ∈ N :=
    IntermediateField.le_normalClosure T
      (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨x, rfl⟩))
  let e : E →ₐ[ℚ] N := f.codRestrict N.toSubalgebra hEN
  letI : Algebra E N := e.toAlgebra
  letI : SMul E N := e.toAlgebra.toSMul
  letI : Module E N := Algebra.toModule
  haveI : IsScalarTower ℚ E N := IsScalarTower.of_algHom e
  let iN : N := ⟨i, IntermediateField.le_normalClosure T
    (IntermediateField.subset_adjoin ℚ _ (Or.inr (Set.mem_singleton i)))⟩
  have hiN : iN ^ 2 = -1 := by apply Subtype.ext; exact hi
  refine ⟨q, hq, ?_⟩
  intro b
  obtain ⟨hprime, hout, hsplit⟩ := (primes b.val).property
  have hnotS : q b ∉ S := fun h => hout (Finset.mem_insert_of_mem h)
  have hnot2 : q b ≠ 2 := fun h => hout (Finset.mem_insert.mpr (Or.inl h))
  have hsplitE :=
    ((discriminantAndSplittingFacts.2.2.2.2 ℚ E N _).mp hsplit).1
  have hsplitF :=
    (discriminantAndSplittingFacts.2.2.2.2 ℚ F E _).mp hsplitE
  refine ⟨hprime, hnotS, hsplit, ?_, hsplitF.1, ?_⟩
  · exact Formalization.Result.helpers.Proposition_3p6.Machinery.split_prime_congruence
      N iN hiN (q b) hprime hnot2 hsplit
  · intro p hp hpprime hpq
    have hidentity : frobeniusClass F E p = {1} :=
      (discriminantAndSplittingFacts.2.2.2.1 F E p).mp
        (hsplitF.2 p hpprime hpq)
    -- A compatible lift has identity restriction to E, hence belongs to Phi(G).
    obtain ⟨σ, hσ⟩ := hfrob p hp hpprime
    refine ⟨hidentity, σ, ?_, hσ⟩
    rw [← hfix, ← IntermediateField.restrictNormalHom_ker]
    change AlgEquiv.restrictNormal σ E = 1
    have hσE := hσ E hE hEGal
    rw [hidentity] at hσE
    exact Set.mem_singleton_iff.mp hσE
  -- HumanLean:proof_end
)
end UnitDistance
