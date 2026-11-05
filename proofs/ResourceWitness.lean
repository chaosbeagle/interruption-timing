import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-! A finite witness selection lemma for resource-obstruction certificates. -/

namespace ResourceWitness

variable {W A : Type*} [DecidableEq W] [DecidableEq A]

/-- Each covered target needs at most one world as its membership witness. -/
theorem cover_by_small_subfamily (B : Finset W) (U : W → Finset A)
    (S : Finset A) (hS : S ⊆ B.biUnion U) :
    ∃ C : Finset W, C ⊆ B ∧ C.card ≤ S.card ∧ S ⊆ C.biUnion U := by
  classical
  have hw : ∀ x : {x // x ∈ S}, ∃ w, w ∈ B ∧ x.val ∈ U w := by
    intro x
    exact Finset.mem_biUnion.mp (hS x.property)
  let f : {x // x ∈ S} → W := fun x => Classical.choose (hw x)
  have hf : ∀ x, f x ∈ B ∧ x.val ∈ U (f x) := by
    intro x
    exact Classical.choose_spec (hw x)
  refine ⟨S.attach.image f, ?_, ?_, ?_⟩
  · intro w hw'
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw'
    exact (hf x).1
  · calc
      (S.attach.image f).card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
  · intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨f ⟨x, hx⟩, ?_, (hf ⟨x, hx⟩).2⟩
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp, rfl⟩

end ResourceWitness

#print axioms ResourceWitness.cover_by_small_subfamily
