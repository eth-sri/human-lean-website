import Formalization.Result.helpers.Proposition_3p8.Machinery
import Formalization.Axioms
import Formalization.Result.Proposition_3p2
import Formalization.Result.Proposition_3p6
import Formalization.Result.Proposition_3p7

noncomputable section
namespace UnitDistance

/-- Proposition 3.8, including all P1–P6 and uniform constants.
The injective field maps implement the nested tower; nonsurjectivity makes
successive inclusions proper. The base is the zeroth admissible field. -/
theorem paper_3_8 :
    ∃ C_F C_H : ℝ, 0 < C_F ∧ 0 < C_H ∧ ∃ ell₀ : ℕ, 2 ≤ ell₀ ∧
      ∀ ell : ℕ, ell₀ ≤ ell →
      ∃ (A : ℕ → AdmissibleDatum) (H : ℝ),
        0 < H ∧ (A 0).t = (ell - 1) ^ 2 / 100 ∧
        (∀ j, (A j).t = (A 0).t ∧ HEq (A j).q (A 0).q) ∧
        Module.finrank ℚ (A 0).L = 3 ∧ IsGalois ℚ (A 0).L ∧
        Nonempty (((A 0).L ≃ₐ[ℚ] (A 0).L) ≃* Multiplicative (ZMod 3)) ∧
        (¬ ∃ ζ : (A 0).L, IsPrimitiveRoot ζ 3) ∧
        Real.log (rootDiscriminant (A 0).L) ≤ C_F * ell * Real.log ell ∧
        (∃ (base : ∀ j, (A 0).L →+* (A j).L)
          (step : ∀ j, (A j).L →+* (A (j + 1)).L),
          base 0 = RingHom.id (A 0).L ∧
          (∀ j, (step j).comp (base j) = base (j + 1)) ∧
          (∀ j, ¬ Function.Surjective (step j)) ∧
          ∀ j,
            letI : Algebra (A 0).L (A j).L := (base j).toAlgebra
            IsGalois (A 0).L (A j).L ∧ everywhereUnramified (A 0).L (A j).L ∧
            IsPGroup 3 ((A j).L ≃ₐ[(A 0).L] (A j).L)) ∧
        Filter.Tendsto (fun j => Module.finrank ℚ (A j).L) Filter.atTop Filter.atTop ∧
        (∀ j, rootDiscriminant (A j).L = rootDiscriminant (A 0).L) ∧
        (∀ j, rootDiscriminant (A j).K ≤ 2 * rootDiscriminant (A 0).L ∧
          (classNumber (A j).K : ℝ) ≤ H ^ Module.finrank ℚ (A j).L) ∧
        Real.log H ≤ C_H * ell * Real.log ell ∧
        0 < translationGrowth (A 0).t H := (by
  -- HumanLean:proof_begin
  classical
  -- Fix all absolute constants before choosing ell or a tower level.
  obtain ⟨C, hC, r, hrmono, hrprime, hrall, hrbound⟩ := primeNumberTheoremModThree
  obtain ⟨Cclass, hCclass, hclass⟩ := paper_3_7
  obtain ⟨C₀, hC₀, hrelations⟩ := shafarevichCubicRelationBound
  let C' : ℝ := max C 1
  have hC' : 1 ≤ C' := le_max_right _ _
  let C_F : ℝ := Real.log (2 * C') / Real.log 2 + 2
  have hC_F : 0 < C_F := by
    have : 0 ≤ Real.log (2 * C') := Real.log_nonneg (by linarith)
    dsimp [C_F]
    positivity
  let C_H : ℝ := 2 * Cclass * (1 + C_F)
  have hC_H : 0 < C_H := by dsimp [C_H]; positivity
  obtain ⟨nH, hnH, hgrowth⟩ :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.eventual_positive_translation_bound
      C_H hC_H
  obtain ⟨nC, hnC⟩ := exists_nat_gt C₀
  refine ⟨C_F, C_H, hC_F, hC_H, max nH (nC + 1), by omega, ?_⟩
  intro ell hell
  have hell100 : 100 ≤ ell := hnH.trans ((le_max_left _ _).trans hell)
  have hell2 : 2 ≤ ell := by omega
  have htpos : 0 < (ell - 1) ^ 2 / 100 := by
    have hfloor :=
      Formalization.Result.helpers.Proposition_3p8.Machinery.quadratic_floor_lower_bound
        ell hell100
    have he : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    have : (0 : ℝ) < (((ell - 1) ^ 2 / 100 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by positivity) hfloor
    exact_mod_cast this
  have hC₀ell : C₀ ≤ (ell - 1 : ℕ) := by
    have : nC ≤ ell - 1 := by omega
    exact hnC.le.trans (by exact_mod_cast this)
  -- Step 1: cubic characters at the first ell primes in the progression.
  have hchars (b : Fin ell) := cyclotomicCharacterFacts.1
    (r b.val) (hrprime b.val).1 (hrprime b.val).2
  choose χ hχconductor hχorder using hchars
  let D : CubicCharacterDatum :=
    { ell := ell
      ell_pos := by omega
      r := fun b => r b.val
      r_prime := fun b => (hrprime b.val).1
      r_distinct := fun _ _ h => Fin.ext (hrmono.injective h)
      r_mod_three := fun b => (hrprime b.val).2
      χ := χ
      primitive := hχconductor
      cubic := hχorder }
  let m := ∏ b, D.r b
  letI : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun b _ => (D.r_prime b).ne_zero)⟩
  let ψ : Fin ell → DirichletCharacter ℂ m := fun b =>
    DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem D.r (Finset.mem_univ b)) (D.χ b)
  let L := fun b => characterFixedField {ψ b}
  let M := ⨆ b, L b
  let F := characterFixedField {∏ b, ψ b}
  letI : Field F := inferInstance
  letI : NumberField F := inferInstance
  letI : Module ℚ F := Algebra.toModule
  obtain ⟨hL, hMdeg, hMGal, hMaut, hreal, hdeg, hGal, haut, hdisc, hFM, hrel⟩ :=
    paper_3_2 D
  have hrealF : totallyReal F := hreal
  have hdegF : Module.finrank ℚ F = 3 := hdeg
  letI : IsGalois ℚ F := hGal
  have hnoζ : ¬ ∃ ζ : F, IsPrimitiveRoot ζ 3 :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.no_cubic_root_of_totallyReal
      F hrealF
  have hlogF : Real.log (rootDiscriminant F) ≤ C_F * ell * Real.log ell := by
    apply Formalization.Result.helpers.Proposition_3p8.Machinery.cubic_log_root_bound
      F ell D.r (fun b => (D.r_prime b).pos) hdegF hdisc C_F hC_F.le hell2
    intro b
    apply Formalization.Result.helpers.Proposition_3p8.Machinery.prime_log_bound
      hC' hell2 (D.r_prime b).pos
    have hk : (b.val + 1 : ℝ) ≤ ell := by exact_mod_cast b.isLt
    have he : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    have hkpos : (0 : ℝ) < b.val + 1 := by positivity
    calc
      (D.r b : ℝ) ≤ C * (b.val + 1) * Real.log (2 * (b.val + 1)) := hrbound b.val
      _ ≤ C' * ell * Real.log (2 * ell) := by
        apply mul_le_mul
        · exact mul_le_mul (le_max_left C 1) hk hkpos.le (by positivity)
        · exact Real.log_le_log (by positivity) (by linarith)
        · apply Real.log_nonneg
          have : (0 : ℝ) ≤ b.val := by positivity
          linarith
        · positivity
  -- The class-field boundary supplies G, its finite generation, and Frobenius lifts.
  let Ω := maximalUnramifiedProPExtension F 3 Nat.prime_three
  letI : Field Ω := inferInstance
  letI : Algebra F Ω := Ω.toSubalgebra.algebra
  letI : SMul F Ω := Ω.toSubalgebra.algebra.toSMul
  letI : Module F Ω := Algebra.toModule
  obtain ⟨hΩ, hfg, hpro, hemb, hunram, hfixed, hfrob⟩ :=
    unramifiedClassFieldCorrespondence F
  letI : IsGalois F Ω := hΩ
  letI : IsTopologicalGroup (Ω ≃ₐ[F] Ω) := inferInstance
  let G := InfiniteGalois.profiniteGalGrp F Ω
  obtain ⟨d, rG, hd, hrG, hrboundG⟩ := hrelations F hrealF hdegF hnoζ hΩ
  have hdlower : ell - 1 ≤ d := by
    letI algFM : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
    letI : SMul F M := algFM.toSMul
    letI : Module F M := Algebra.toModule
    letI : IsGalois F M := hrel.1
    let eM : (M ≃ₐ[F] M) ≃* (Fin (ell - 1) → Multiplicative (ZMod 3)) := hrel.2.1.some
    have hMpro : IsPGroup 3 (M ≃ₐ[F] M) := by
      apply IsPGroup.of_card (n := ell - 1)
      exact (Nat.card_congr eM.toEquiv).trans (by simp)
    let e : M →ₐ[F] Ω := (hemb M hrel.2.2 hMpro).some
    exact Formalization.Result.helpers.Proposition_3p8.Machinery.embedded_elementary_quotient_rank_bound
      F M Ω (ell - 1) d e eM hd
  -- Step 2 begins with the fixed Chebotarev primes in the finite Frattini field.
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq
    (-1 : AlgebraicClosure F) (by norm_num : 0 < 2)
  obtain ⟨hE, hEGal, hN, q, hq, hqprops⟩ := paper_3_6 F hrealF hdegF i hi
    ((ell - 1) ^ 2 / 100) htpos (3 * m).primeFactors
  let t : ℕ := (ell - 1) ^ 2 / 100
  have hprimes (b : Fin t) :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.enumerate_split_primes
      F (q b) (hqprops b).2.2.2.2.1
  rw [hdegF] at hprimes
  choose p hp hpall using hprimes
  -- At the cubic base each q_b has three primes, hence there are 3t relations.
  have hlifts (b : Fin t) (a : Fin 3) :=
    ((hqprops b).2.2.2.2.2 (p b a) (hp b a).1 (hp b a).2.1 (hp b a).2.2).2
  choose σ hσΦ hσfrob using hlifts
  let g : Fin (t * 3) → G := fun v =>
    σ (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2
  have hgΦ (v : Fin (t * 3)) : g v ∈ frattiniSubgroup G :=
    hσΦ (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2
  let killed : Subgroup G := (Subgroup.normalClosure (Set.range g)).topologicalClosure
  letI : killed.Normal := Subgroup.is_normal_topologicalClosure _
  have hkilled_closed : IsClosed (killed : Set G) :=
    Subgroup.isClosed_topologicalClosure _
  letI : IsClosed (killed : Set G) := hkilled_closed
  letI : TotallyDisconnectedSpace (G ⧸ killed) :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.quotient_totally_disconnected
      G killed hkilled_closed
  let Gbar := ProfiniteGrp.of (G ⧸ killed)
  let π : ContinuousMonoidHom G Gbar :=
    { toMonoidHom := QuotientGroup.mk' killed
      continuous_toFun := QuotientGroup.continuous_mk }
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective
  have hπker : π.toMonoidHom.ker = killed := QuotientGroup.ker_mk' killed
  have hcut := (frattiniQuotientFacts 3 Nat.prime_three G hpro hfg).2.2
    (t * 3) g hgΦ Gbar π hπ hπker
  have hdbar : generatorRank Gbar = (d : ℕ∞) := hcut.1.trans hd
  have hrbar := hcut.2 (by rw [hrG]; exact ENat.coe_lt_top _)
  have hrbar_fin : relationRank 3 Nat.prime_three Gbar < ⊤ :=
    lt_of_le_of_lt hrbar (by rw [hrG, ← ENat.coe_add]; exact ENat.coe_lt_top _)
  obtain ⟨rbar, hrbar_eq⟩ := ENat.ne_top_iff_exists.mp hrbar_fin.ne
  have hrbar_nat : rbar ≤ rG + 3 * t := by
    rw [← hrbar_eq, hrG] at hrbar
    exact_mod_cast (by simpa only [Nat.mul_comm, ← ENat.coe_add] using hrbar :
      (rbar : ℕ∞) ≤ ((rG + 3 * t : ℕ) : ℕ∞))
  have hprobar :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.pro_three_of_continuous_surjection
      G Gbar hpro π hπ
  letI : Nontrivial Gbar :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.nontrivial_of_positive_generator_rank
      Gbar d (by omega) hdbar
  have hGS : 4 * rbar ≤ d ^ 2 :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.cutting_relation_inequality
      ell d rG rbar C₀ (by omega) hC₀ell hdlower hrboundG hrbar_nat
  letI : Infinite Gbar := golodShafarevichCriterion Gbar hprobar d rbar hdbar hrbar_eq.symm hGS
  -- Step 3: recursively shrink open normal subgroups in the infinite quotient.
  let topOpen : OpenNormalSubgroup Gbar :=
    { toSubgroup := ⊤, isOpen' := isOpen_univ }
  have hsmaller (U : OpenNormalSubgroup Gbar) :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.exists_smaller_open_normal
      Gbar U
  choose shrink hshrink using hsmaller
  let chain : ℕ → OpenNormalSubgroup Gbar := fun j => (shrink^[j]) topOpen
  have hchain0 : chain 0 = topOpen := rfl
  have hchainsucc (j : ℕ) : chain (j + 1) < chain j := by
    simpa only [chain, Function.iterate_succ_apply'] using hshrink (chain j)
  have hindexmono : StrictMono (fun j => (chain j).toSubgroup.index) := by
    apply strictMono_nat_of_lt_succ
    intro j
    letI := (chain (j + 1)).toOpenSubgroup.finiteIndex_of_finite_quotient
    exact Subgroup.index_strictAnti (hchainsucc j)
  have hindexgrow : Filter.Tendsto (fun j => (chain j).toSubgroup.index)
      Filter.atTop Filter.atTop := hindexmono.tendsto_atTop
  let upstairs : ℕ → Subgroup G := fun j => (chain j).toSubgroup.comap π.toMonoidHom
  have hupnormal (j : ℕ) : (upstairs j).Normal := inferInstance
  have hupopen (j : ℕ) : IsOpen (upstairs j : Set G) :=
    (chain j).toOpenSubgroup.isOpen.preimage π.continuous
  let fields : ℕ → IntermediateField F Ω := fun j => IntermediateField.fixedField (upstairs j)
  letI (j : ℕ) : Algebra F (fields j) := (fields j).toSubalgebra.algebra
  letI (j : ℕ) : SMul F (fields j) := (fields j).toSubalgebra.algebra.toSMul
  letI (j : ℕ) : Module F (fields j) := Algebra.toModule
  letI (j : ℕ) : Module.Free F (fields j) := Module.Free.of_divisionRing F (fields j)
  have hfields (j : ℕ) := hfixed (upstairs j) (hupnormal j) (hupopen j)
  choose hnumber hfieldGal hfielddeg hfieldfix using hfields
  letI (j : ℕ) : NumberField (fields j) := hnumber j
  letI (j : ℕ) : Module ℚ (fields j) := Algebra.toModule
  letI (j : ℕ) : IsScalarTower ℚ F (fields j) :=
    IsScalarTower.of_algebraMap_eq (fun x => by simp)
  letI (j : ℕ) : FiniteDimensional F (fields j) := FiniteDimensional.right ℚ F (fields j)
  letI (j : ℕ) : IsGalois F (fields j) := hfieldGal j
  have hfield_unram (j : ℕ) : everywhereUnramified F (fields j) ∧
      IsPGroup 3 ((fields j) ≃ₐ[F] (fields j)) :=
    hunram (fields j) (hnumber j) (hfieldGal j)
  have hfieldreal (j : ℕ) : totallyReal (fields j) := by
    intro τ x
    exact (hfield_unram j).1.2 τ (hrealF (τ.comp (algebraMap F (fields j)))) x
  have hfieldroot (j : ℕ) : rootDiscriminant (fields j) = rootDiscriminant F :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.unramified_root_discriminant
      F (fields j) (hfield_unram j).1
  have hfielddeg' (j : ℕ) : Module.finrank F (fields j) = (chain j).toSubgroup.index :=
    (hfielddeg j).trans ((chain j).toSubgroup.index_comap_of_surjective hπ)
  have habsdeg (j : ℕ) : Module.finrank ℚ (fields j) = 3 * (chain j).toSubgroup.index := by
    rw [← Module.finrank_mul_finrank ℚ F (fields j), hdegF, hfielddeg' j]
  have hdegreegrow : Filter.Tendsto (fun j => Module.finrank ℚ (fields j))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun j => by rw [habsdeg j]; omega) hindexgrow
  have hchainanti : Antitone chain := antitone_nat_of_succ_le (fun j => (hchainsucc j).le)
  have hupanti : Antitone upstairs := fun _ _ hij => Subgroup.comap_mono (hchainanti hij)
  have hfieldmono : Monotone fields := fun _ _ hij => IntermediateField.fixedField_le (hupanti hij)
  have hidentity_frobenius (j : ℕ) (b : Fin t) (P : Ideal (NumberField.RingOfIntegers F))
      (hP : P.IsPrime)
      (hPq : P.comap (algebraMap (NumberField.RingOfIntegers ℚ)
        (NumberField.RingOfIntegers F)) = Ideal.span {(q b : NumberField.RingOfIntegers ℚ)}) :
      (1 : (fields j) ≃ₐ[F] (fields j)) ∈ frobeniusClass F (fields j) P := by
    obtain ⟨a, ha⟩ := hpall b P hP hPq
    have hmem : σ b a ∈ killed := by
      apply (Subgroup.le_topologicalClosure (Subgroup.normalClosure (Set.range g)))
      apply Subgroup.subset_normalClosure (s := Set.range g)
      exact ⟨finProdFinEquiv (b, a), congrArg (fun v : Fin t × Fin 3 => σ v.1 v.2)
        (finProdFinEquiv.symm_apply_apply (b, a))⟩
    have hπσ : π (σ b a) = 1 := by
      change σ b a ∈ π.toMonoidHom.ker
      rw [hπker]
      exact hmem
    have hfix : σ b a ∈ upstairs j := by
      change π (σ b a) ∈ (chain j).toSubgroup
      rw [hπσ]
      exact Subgroup.one_mem _
    rw [← hfieldfix j, ← IntermediateField.restrictNormalHom_ker] at hfix
    change AlgEquiv.restrictNormal (σ b a) (fields j) = 1 at hfix
    have hf := hσfrob b a (fields j) (hnumber j) (hfieldGal j)
    rw [hfix, ha] at hf
    exact hf
  have hqsplit (j : ℕ) (b : Fin t) :
      completelySplit ℚ (fields j) (Ideal.span {(q b : NumberField.RingOfIntegers ℚ)}) := by
    apply (discriminantAndSplittingFacts.2.2.2.2 ℚ F (fields j) _).mpr
    refine ⟨(hqprops b).2.2.2.2.1, ?_⟩
    intro P hP hPq
    apply (discriminantAndSplittingFacts.2.2.2.1 F (fields j) P).mpr
    exact Formalization.Result.helpers.Proposition_3p8.Machinery.frobenius_class_singleton_of_identity
      F (fields j) P (hidentity_frobenius j b P hP hPq)
  have hup0 : upstairs 0 = ⊤ := by
    change (chain 0).toSubgroup.comap π.toMonoidHom = ⊤
    rw [hchain0]
    exact Subgroup.comap_top _
  have hfield0 : fields 0 = ⊥ := by
    change IntermediateField.fixedField (upstairs 0) = ⊥
    rw [hup0]
    exact InfiniteGalois.fixedField_bot (k := F) (K := Ω)
  let e0 : F ≃ₐ[F] (fields 0) :=
    (Formalization.Result.helpers.Proposition_3p8.Machinery.base_equiv_of_bottom
      F Ω (fields 0) hfield0).some
  have hbase_degree : Module.finrank ℚ (fields 0) = 3 := by
    rw [habsdeg, hchain0]
    simp [topOpen]
  have hbase_Galois : IsGalois ℚ (fields 0) := IsGalois.of_algEquiv (e0.restrictScalars ℚ)
  have hbase_cyclic : Nonempty (((fields 0) ≃ₐ[ℚ] (fields 0)) ≃* Multiplicative (ZMod 3)) :=
    ⟨(AlgEquiv.autCongr (e0.restrictScalars ℚ)).symm.trans haut.some⟩
  let base : ∀ j, (fields 0) →+* (fields j) := fun j =>
    (IntermediateField.inclusion (hfieldmono (Nat.zero_le j))).toRingHom
  let step : ∀ j, (fields j) →+* (fields (j + 1)) := fun j =>
    (IntermediateField.inclusion (hfieldmono (Nat.le_succ j))).toRingHom
  have hbase0 : base 0 = RingHom.id (fields 0) := by ext x; rfl
  have hcomp (j : ℕ) : (step j).comp (base j) = base (j + 1) := by ext x; rfl
  have hproper (j : ℕ) : ¬ Function.Surjective (step j) := by
    intro hs
    have hfields_eq : fields j = fields (j + 1) :=
      SetLike.coe_injective (Set.eq_of_inclusion_surjective
        (h := hfieldmono (Nat.le_succ j)) hs)
    have hups_eq : upstairs j = upstairs (j + 1) := by
      rw [← hfieldfix j, ← hfieldfix (j + 1)]
      exact congrArg IntermediateField.fixingSubgroup hfields_eq
    have hchain_eq : (chain j).toSubgroup = (chain (j + 1)).toSubgroup :=
      Subgroup.comap_injective hπ hups_eq
    exact (hchainsucc j).ne (SetLike.coe_injective (congrArg (fun U : Subgroup Gbar => (U : Set Gbar))
      hchain_eq.symm))
  have hlayer (j : ℕ) :
      letI : Algebra (fields 0) (fields j) := (base j).toAlgebra
      IsGalois (fields 0) (fields j) ∧ everywhereUnramified (fields 0) (fields j) ∧
        IsPGroup 3 ((fields j) ≃ₐ[fields 0] (fields j)) := by
    letI : Algebra (fields 0) (fields j) := (base j).toAlgebra
    letI : SMul (fields 0) (fields j) := (base j).toAlgebra.toSMul
    letI : Module (fields 0) (fields j) := Algebra.toModule
    letI : IsScalarTower F (fields 0) (fields j) := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    letI : IsScalarTower ℚ (fields 0) (fields j) :=
      IsScalarTower.of_algebraMap_eq (fun x => by simp)
    letI : IsGalois (fields 0) (fields j) := IsGalois.tower_top_of_isGalois F (fields 0) (fields j)
    refine ⟨inferInstance, ?_, ?_⟩
    · exact Formalization.Result.helpers.Proposition_3p8.Machinery.unramified_of_equal_root_discriminant
        (fields 0) (fields j) (hfieldreal j) ((hfieldroot j).trans (hfieldroot 0).symm)
    · have hdegrel : Module.finrank (fields 0) (fields j) = Module.finrank F (fields j) := by
        have hmul := Module.finrank_mul_finrank F (fields 0) (fields j)
        have hz : Module.finrank F (fields 0) = 1 := by
          rw [hfielddeg', hchain0]
          simp [topOpen]
        simpa only [hz, one_mul] using hmul
      obtain ⟨n, hn⟩ := (hfield_unram j).2.exists_card_eq
      apply IsPGroup.of_card (n := n)
      rw [IsGalois.card_aut_eq_finrank, hdegrel, ← IsGalois.card_aut_eq_finrank F (fields j)]
      exact hn
  -- Step 4's constant is already fixed independently of every finite layer.
  let H : ℝ := (2 * rootDiscriminant F) ^ (2 * Cclass)
  have hrootF : 1 ≤ rootDiscriminant F :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.root_discriminant_ge_one F
  have hH : 0 < H := Real.rpow_pos_of_pos (by positivity) _
  have hlogH : Real.log H ≤ C_H * ell * Real.log ell :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.log_class_constant_bound
      (rootDiscriminant F) Cclass C_F hrootF hCclass.le ell hell2 hlogF
  have hpositive : 0 < translationGrowth t H := by
    have hgrowth' := hgrowth ell ((le_max_left _ _).trans hell)
    unfold translationGrowth
    dsimp only [t]
    linarith
  -- Adjoin i to each real layer, keeping the same t and rational primes.
  have hCM (j : ℕ) :=
    Formalization.Result.helpers.Proposition_3p8.Machinery.exists_imaginary_quadratic_extension
      (fields j) (hfieldreal j)
  choose K hK hNK hLK iCM cCM hiCM hgenCM hcCM using hCM
  letI (j : ℕ) : Field (K j) := hK j
  letI (j : ℕ) : NumberField (K j) := hNK j
  letI (j : ℕ) : Algebra (fields j) (K j) := hLK j
  let A : ℕ → AdmissibleDatum := fun j =>
    { L := fields j
      K := K j
      realL := hfieldreal j
      i := iCM j
      i_sq := hiCM j
      generated := hgenCM j
      c := cCM j
      c_ne_one := hcCM j
      t := t
      t_pos := htpos
      q := q
      q_prime := fun b => (hqprops b).1
      q_distinct := hq
      q_mod_four := fun b => (hqprops b).2.2.2.1
      q_split := hqsplit j }
  refine ⟨A, H, hH, rfl, (fun _ => ⟨rfl, HEq.rfl⟩), hbase_degree,
    hbase_Galois, hbase_cyclic, ?_, ?_, ?_, hdegreegrow, ?_, ?_, hlogH, hpositive⟩
  · exact Formalization.Result.helpers.Proposition_3p8.Machinery.no_cubic_root_of_totallyReal
      (fields 0) (hfieldreal 0)
  · change Real.log (rootDiscriminant (fields 0)) ≤ _
    rw [hfieldroot 0]
    exact hlogF
  · exact ⟨base, step, hbase0, hcomp, hproper, hlayer⟩
  · intro j
    exact (hfieldroot j).trans (hfieldroot 0).symm
  · intro j
    have hcm :=
      Formalization.Result.helpers.Proposition_3p8.Machinery.quadratic_cm_root_bound (A j)
    change rootDiscriminant (K j) ≤ 2 * rootDiscriminant (fields j) at hcm
    rw [hfieldroot j] at hcm
    refine ⟨?_, ?_⟩
    · change rootDiscriminant (K j) ≤ 2 * rootDiscriminant (fields 0)
      rw [hfieldroot 0]
      exact hcm
    · have hKdeg := (idealArithmeticFacts.2 (A j).L (A j).K (A j).realL
        (A j).i (A j).i_sq (A j).generated (A j).c (A j).c_ne_one).2.1
      exact Formalization.Result.helpers.Proposition_3p8.Machinery.class_bound_with_fixed_root
        (K j) Cclass (rootDiscriminant F) hCclass.le hrootF
        (Module.finrank ℚ (fields j)) hKdeg hcm (hclass (K j)).1
  -- HumanLean:proof_end
)
end UnitDistance
