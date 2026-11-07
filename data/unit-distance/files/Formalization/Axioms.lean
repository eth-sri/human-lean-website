import Formalization.Definition
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.FieldTheory.LinearDisjoint

/-! Explicit external trust from the approved PDF-derived contract.
Each declaration is a mapped external premise. The paper-specific counting,
averaging, conductor exponents, tower construction and bounds are theorem goals.
Standard ideal factorization and Galois correspondence APIs are also imported. -/

noncomputable section
open scoped NumberField nonZeroDivisors ENNReal
open Set
namespace UnitDistance

/-- Neukirch VII §13: only the completely split Chebotarev case. -/
axiom chebotarevSplitPrimes (N : Type) [Field N] [NumberField N] [IsGalois ℚ N]
    (S : Finset ℕ) :
    Set.Infinite {q : ℕ | q.Prime ∧ q ∉ S ∧
      completelySplit ℚ N (Ideal.span {(q : 𝓞 ℚ)})}

/-- General arithmetic facts from Neukirch I §§1–5.
Unique factorization, transport of ideals and multiplicativity of ideal norms
also have their ordinary library interfaces; no counting inequality is assumed. -/
axiom idealArithmeticFacts :
    (∀ (K : Type) [Field K] [NumberField K],
      (∀ I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        (I = J ↔ ∀ P, idealValuation P I = idealValuation P J) ∧
        (∀ P, idealValuation P (I * J) = idealValuation P I + idealValuation P J) ∧
        (ClassGroup.mk I = ClassGroup.mk J ↔ ∃ x : Kˣ,
          (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * (J : FractionalIdeal (𝓞 K)⁰ K))) ∧
      (∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ↔ ∀ P, 0 ≤ idealValuation P I) ∧
      (∀ β : 𝓞 K, β ≠ 0 → ∃ z : ℤ, z ≠ 0 ∧ Algebra.norm ℚ (β : K) = (z : ℚ)) ∧
      (∀ (n : ℕ) (σ : Fin n → (K →+* ℂ)), Function.Bijective σ →
        ∀ x : K, (∏ j, σ j x) = (Algebra.norm ℚ x : ℂ))) ∧
    (∀ (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K]
      [Algebra L K], totallyReal L → ∀ i : K, i ^ 2 = -1 →
      Algebra.adjoin L {i} = ⊤ → ∀ c : K ≃ₐ[L] K, c ≠ 1 →
      Module.finrank L K = 2 ∧ Module.finrank ℚ K = 2 * Module.finrank ℚ L ∧
      (∀ (σ : K →+* ℂ) (x : K), σ (c x) = star (σ x)))

/-- Discriminants, unramified primes and finite splitting in towers.
These are general identities, without a root-discriminant or tower bound. -/
axiom discriminantAndSplittingFacts :
    (∀ (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
      [Algebra F M],
      absoluteDiscriminant M = absoluteDiscriminant F ^ Module.finrank F M *
        (relativeDiscriminant F M).absNorm ∧
      ((relativeDiscriminant F M = ⊤) ↔
        ∀ (p : Ideal (𝓞 F)) (P : Ideal (𝓞 M)), p ≠ ⊥ → p.IsPrime → P.IsPrime →
          P.comap (algebraMap (𝓞 F) (𝓞 M)) = p → p.ramificationIdx P = 1)) ∧
    (∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I.absNorm = 1 ↔ I = ⊤) ∧
    (∀ (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K]
      [Algebra L K], totallyReal L → ∀ i : K, i ^ 2 = -1 →
      Algebra.adjoin L {i} = ⊤ →
      (relativeDiscriminant L K ∣ Ideal.span {(4 : 𝓞 L)}) ∧
      (∀ p : Ideal (𝓞 L), p ≠ ⊥ → p.IsPrime → (2 : 𝓞 L) ∉ p →
        (completelySplit L K p ↔ ∃ a b : (𝓞 L) ⧸ p,
          a ≠ b ∧ a ^ 2 + 1 = 0 ∧ b ^ 2 + 1 = 0))) ∧
    (∀ (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
      [Algebra F M] [IsGalois F M] (p : Ideal (𝓞 F)),
      completelySplit F M p ↔ frobeniusClass F M p = {1}) ∧
    (∀ (F M N : Type) [Field F] [NumberField F] [Field M] [NumberField M]
      [Field N] [NumberField N] [Algebra F M] [Algebra M N] [Algebra F N]
      [IsScalarTower F M N] (p : Ideal (𝓞 F)),
      completelySplit F N p ↔ completelySplit F M p ∧
        ∀ P : Ideal (𝓞 M), P.IsPrime →
          P.comap (algebraMap (𝓞 F) (𝓞 M)) = p → completelySplit M N P)

/-- The full lattice theorem for a nonzero fractional ideal and one embedding
from each conjugate pair. The window unfolding identity is not an axiom. -/
axiom minkowskiFractionalIdealLattice (K : Type) [Field K] [NumberField K]
    (f : ℕ) (σ : Fin f → (K →+* ℂ))
    (hpairs : Function.Bijective (fun jb : Fin f × Bool =>
      if jb.2 then (starRingEnd ℂ).comp (σ jb.1) else σ jb.1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (Λ : Submodule ℤ (Fin f → ℂ))
    (hΛ : (Λ : Set (Fin f → ℂ)) =
      {z | ∃ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), ∀ j, z j = σ j x}) :
    ∃ b : Module.Basis (Fin (2 * f)) ℝ (Fin f → ℂ),
      Λ = Submodule.span ℤ (Set.range b) ∧
      ∃ T : Set (Fin f → ℂ), MeasurableSet T ∧ Bornology.IsBounded T ∧
        MeasureTheory.IsAddFundamentalDomain Λ T ∧
        0 < MeasureTheory.volume T ∧ MeasureTheory.volume T < ⊤

/-- Only the Minkowski representative bound, with the signature factor. -/
axiom minkowskiIdealClassBound (K : Type) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      ((I : Ideal (𝓞 K)).absNorm : ℝ) ≤
        (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        ((Nat.factorial (Module.finrank ℚ K) : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K) *
        Real.sqrt (absoluteDiscriminant K : ℝ)

section
attribute [local instance 2000] CyclotomicField.algebra

/-- Prime cubic characters and the general conductor–discriminant formula.
CRT and character multiplication retain their native library meanings. -/
axiom cyclotomicCharacterFacts :
    (∀ (r : ℕ) (hr : r.Prime), r % 3 = 1 →
      ∃ χ : DirichletCharacter ℂ r, characterConductor χ = r ∧ orderOf χ = 3) ∧
    (∀ (r : ℕ) [NeZero r], r.Prime → r % 3 = 1 →
      ∀ χ : DirichletCharacter ℂ r, characterConductor χ = r → orderOf χ = 3 →
      let L := characterFixedField {χ}
      totallyReal L ∧ fieldConductor L = r ∧ Module.finrank ℚ L = 3 ∧
      IsGalois ℚ L ∧ Nonempty ((L ≃ₐ[ℚ] L) ≃* Multiplicative (ZMod 3)) ∧
      (∀ q : ℕ, q.Prime → q ≠ r → ∀ P : Ideal (𝓞 L), P.IsPrime →
        P.comap (algebraMap (𝓞 ℚ) (𝓞 L)) = Ideal.span {(q : 𝓞 ℚ)} →
        (Ideal.span {(q : 𝓞 ℚ)}).ramificationIdx P = 1)) ∧
    (∀ (m : ℕ) [NeZero m] (X : Subgroup (DirichletCharacter ℂ m)) [Fintype X],
      absoluteDiscriminant (characterFixedField (X : Set (DirichletCharacter ℂ m))) =
        ∏ χ : X, characterConductor χ.val) ∧
    (∀ (a b : ℕ) [NeZero a] [NeZero b], Nat.Coprime a b →
      ∀ (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b),
      characterConductor χ = a → characterConductor ψ = b →
      characterConductor ((DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ) *
        (DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ)) = a * b)
end

/-- Prime number theorem consequence for the fixed progression 1 modulo 3. -/
axiom primeNumberTheoremModThree :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ k, (r k).Prime ∧ r k % 3 = 1) ∧
      (∀ q : ℕ, q.Prime → q % 3 = 1 → ∃ k, r k = q) ∧
      ∀ k, (r k : ℝ) ≤ C * (k + 1) * Real.log (2 * (k + 1))

/-- General Frattini and basis facts; the relations are any chosen elements
of the Frattini subgroup, not specifically the paper's Frobenius elements. -/
axiom frattiniQuotientFacts (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp.{0})
    (hpro : ∀ (N : Subgroup G) (hN : N.Normal), IsOpen (N : Set G) →
      letI := hN
      IsPGroup p (G ⧸ N)) (hfg : generatorRank G < ⊤) :
    frattiniSubgroup G =
      (Subgroup.closure ({x | ∃ g : G, x = g ^ p} ∪
        {x | ∃ g h : G, x = g * h * g⁻¹ * h⁻¹})).topologicalClosure ∧
    (∃ hΦ : (frattiniSubgroup G).Normal,
      letI := hΦ
      IsOpen (frattiniSubgroup G : Set G) ∧
      ∃ d : ℕ, generatorRank G = (d : ℕ∞) ∧
        Nonempty ((G ⧸ frattiniSubgroup G) ≃* (Fin d → Multiplicative (ZMod p)))) ∧
    (∀ (k : ℕ) (g : Fin k → G), (∀ j, g j ∈ frattiniSubgroup G) →
      ∀ (H : ProfiniteGrp.{0}) (π : ContinuousMonoidHom G H), Function.Surjective π →
      π.toMonoidHom.ker = (Subgroup.normalClosure (Set.range g)).topologicalClosure →
      generatorRank H = generatorRank G ∧
        (relationRank p hp G < ⊤ → relationRank p hp H ≤ relationRank p hp G + k))

/-- Golod–Shafarevich at the odd prime 3, with nontriviality explicit. -/
axiom golodShafarevichCriterion (G : ProfiniteGrp.{0}) [Nontrivial G]
    (hpro : ∀ (N : Subgroup G) (hN : N.Normal), IsOpen (N : Set G) →
      letI := hN
      IsPGroup 3 (G ⧸ N)) (d r : ℕ)
    (hd : generatorRank G = (d : ℕ∞))
    (hr : relationRank 3 Nat.prime_three G = (r : ℕ∞))
    (hineq : 4 * r ≤ d ^ 2) : Infinite G

/-- Unramified class field theory and its profinite Galois correspondence.
The last clause gives compatible Frobenius representatives, without imposing
any splitting on any chosen infinite extension. -/
axiom unramifiedClassFieldCorrespondence (F : Type) [Field F] [NumberField F] :
    let Ω := maximalUnramifiedProPExtension F 3 Nat.prime_three
    IsGalois F Ω ∧ generatorRank (Ω ≃ₐ[F] Ω) < ⊤ ∧
    (∀ (N : Subgroup (Ω ≃ₐ[F] Ω)) (hN : N.Normal), IsOpen (N : Set (Ω ≃ₐ[F] Ω)) →
      letI := hN
      IsPGroup 3 ((Ω ≃ₐ[F] Ω) ⧸ N)) ∧
    (∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
      everywhereUnramified F M → IsPGroup 3 (M ≃ₐ[F] M) → Nonempty (M →ₐ[F] Ω)) ∧
    (∀ E : IntermediateField F Ω, ∀ hE : NumberField E,
      letI := hE
      IsGalois F E → everywhereUnramified F E ∧ IsPGroup 3 (E ≃ₐ[F] E)) ∧
    (∀ (N : Subgroup (Ω ≃ₐ[F] Ω)) (hN : N.Normal), IsOpen (N : Set (Ω ≃ₐ[F] Ω)) →
      let E := IntermediateField.fixedField N
      ∃ hE : NumberField E,
        letI := hE
        IsGalois F E ∧ Module.finrank F E = N.index ∧ E.fixingSubgroup = N) ∧
    (∀ p : Ideal (𝓞 F), p ≠ ⊥ → p.IsPrime →
      ∃ σ : Ω ≃ₐ[F] Ω, ∀ E : IntermediateField F Ω, ∀ hE : NumberField E,
        letI := hE
        ∀ hGal : IsGalois F E,
          letI := hGal
          AlgEquiv.restrictNormal σ E ∈ frobeniusClass F E p)

/-- Shafarevich's uniform relation estimate for totally real cubic bases only. -/
axiom shafarevichCubicRelationBound :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (F : Type) [Field F] [NumberField F],
      totallyReal F → Module.finrank ℚ F = 3 →
      (¬ ∃ ζ : F, IsPrimitiveRoot ζ 3) →
      let Ω := maximalUnramifiedProPExtension F 3 Nat.prime_three
      ∀ hGal : IsGalois F Ω,
        letI := hGal
        let G := InfiniteGalois.profiniteGalGrp F Ω
        ∃ d r : ℕ, generatorRank G = (d : ℕ∞) ∧
          relationRank 3 Nat.prime_three G = (r : ℕ∞) ∧ (r : ℝ) ≤ d + C₀

end UnitDistance
