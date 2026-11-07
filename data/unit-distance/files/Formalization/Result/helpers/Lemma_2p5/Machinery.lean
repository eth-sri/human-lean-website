import Formalization.Axioms
import Formalization.Definition
import Formalization.Result.Proposition_2p2
import Formalization.Result.Lemma_2p4
import Mathlib

namespace Formalization.Result.helpers.Lemma_2p5.Machinery



/-- Remembering one endpoint distinguishes the two orientations of a segment. -/
lemma ordered_unit_pairs_bound (P : Set ℂ) (hP : P.Finite) :
    Nat.card {e : ℂ × ℂ // e.1 ∈ P ∧ e.2 ∈ P ∧ dist e.1 e.2 = 1} ≤
      2 * UnitDistance.unitDistanceCount P := by
  classical
  let S := {s : Finset ℂ // (↑s : Set ℂ) ⊆ P ∧ s.card = 2 ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → dist x y = 1}
  letI : Finite S := Finite.of_injective
    (fun s : S => (⟨s.val, Finset.mem_powerset.mpr (by
      intro x hx
      exact hP.mem_toFinset.mpr (s.property.1 hx))⟩ : ↥(hP.toFinset.powerset)))
    (by
      intro s t h
      apply Subtype.ext
      exact congrArg (fun v : ↥(hP.toFinset.powerset) => v.val) h)
  letI : Fintype S := Fintype.ofFinite S
  let O := {e : ℂ × ℂ // e.1 ∈ P ∧ e.2 ∈ P ∧ dist e.1 e.2 = 1}
  have hne (e : O) : e.val.1 ≠ e.val.2 := by
    intro h
    have := e.property.2.2
    rw [h, dist_self] at this
    norm_num at this
  let segment (e : O) : S := ⟨{e.val.1, e.val.2}, by
    refine ⟨?_, by simp [hne e], ?_⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact e.property.1
      · exact e.property.2.1
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact e.property.2.2
      · exact (dist_comm _ _).trans e.property.2.2
      · exact (hxy rfl).elim⟩
  let mark (e : O) : (s : S) × ↥s.val :=
    ⟨segment e, ⟨e.val.1, by simp [segment]⟩⟩
  have hinj : Function.Injective mark := by
    intro e f h
    have hs : ({e.val.1, e.val.2} : Finset ℂ) = {f.val.1, f.val.2} :=
      congrArg (fun v : (s : S) × ↥s.val => v.1.val) h
    have hx : e.val.1 = f.val.1 :=
      congrArg (fun v : (s : S) × ↥s.val => (v.2 : ℂ)) h
    have hm : e.val.2 ∈ ({f.val.1, f.val.2} : Finset ℂ) := by
      rw [← hs]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hy : e.val.2 = f.val.2 := hm.resolve_left (by
      intro he
      exact hne e (hx.trans he.symm))
    exact Subtype.ext (Prod.ext hx hy)
  calc
    Nat.card O ≤ Nat.card ((s : S) × ↥s.val) := Nat.card_le_card_of_injective mark hinj
    _ = 2 * UnitDistance.unitDistanceCount P := by
      rw [Nat.card_sigma]
      have hc : ∀ s : S, Nat.card ↥s.val = 2 := fun s => by
        simpa using s.property.2.1
      simp_rw [hc]
      simp [UnitDistance.unitDistanceCount, S, Nat.card_eq_fintype_card, mul_comm]



end Formalization.Result.helpers.Lemma_2p5.Machinery
