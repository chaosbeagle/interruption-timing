import ReserveThreshold
import ResourceWitness
import Mathlib.Data.Finset.Range

/-!
# Small certificates of resource infeasibility

At budget `k`, every infeasible finite information set has an infeasible
subfamily containing at most `k+1` worlds. This bound is sharp for every `k`.
-/

namespace ResourceObstruction

open ReserveThreshold

variable {α Θ : Type*} [DecidableEq α] [DecidableEq Θ]

omit [DecidableEq Θ] in
theorem mandatory_mono {B C : Finset Θ} (U : Θ → Finset α) (hCB : C ⊆ B) :
    mandatory C U ⊆ mandatory B U := Finset.biUnion_subset_biUnion_of_subset_left U hCB

omit [DecidableEq Θ] in
theorem infeasible_of_mandatory_card (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) (hc : k < (mandatory B U).card) :
    ¬ Feasible B U L r k := by
  intro h
  have hm := ((feasible_iff_pointwise B U L r k).mp h).1
  omega

/-- A cardinality violation alone needs at most `k+1` urgent-target witnesses. -/
theorem urgent_obstruction (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) (hc : k < (mandatory B U).card) :
    ∃ C ⊆ B, C.card ≤ k + 1 ∧ ¬ Feasible C U L r k := by
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (by omega :
    k + 1 ≤ (mandatory B U).card)
  obtain ⟨C, hCB, hCcard, hcover⟩ :=
    ResourceWitness.cover_by_small_subfamily B U S hS
  refine ⟨C, hCB, by omega, infeasible_of_mandatory_card C U L r k ?_⟩
  have hh := Finset.card_le_card hcover
  change S.card ≤ (mandatory C U).card at hh
  omega

/-- Exact finite obstruction bound. One world witnesses late demand; at most
`k` further worlds witness all the mandatory early targets. -/
theorem small_obstruction (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) (hbad : ¬ Feasible B U L r k) :
    ∃ C ⊆ B, C.card ≤ k + 1 ∧ ¬ Feasible C U L r k := by
  classical
  by_cases hc : (mandatory B U).card ≤ k
  · have hn : ¬ ∀ θ ∈ B, cost (L θ) (mandatory B U) (r θ) ≤ k := by
      intro h
      exact hbad ((feasible_iff_pointwise B U L r k).mpr ⟨hc, h⟩)
    obtain ⟨θ, hθ⟩ := Classical.not_forall.mp hn
    have hθB : θ ∈ B := by
      by_contra h
      exact hθ (fun ht => False.elim (h ht))
    have hcost : ¬ cost (L θ) (mandatory B U) (r θ) ≤ k := by
      intro h
      exact hθ (fun _ => h)
    obtain ⟨C, hCB, hCcard, hcover⟩ :=
      ResourceWitness.cover_by_small_subfamily B U (mandatory B U) (Finset.Subset.refl _)
    let D := insert θ C
    have hDB : D ⊆ B := Finset.insert_subset hθB hCB
    have hCD : C ⊆ D := Finset.subset_insert _ _
    have hsame : mandatory D U = mandatory B U := by
      apply Finset.Subset.antisymm (mandatory_mono U hDB)
      exact Finset.Subset.trans hcover (mandatory_mono U hCD)
    refine ⟨D, hDB, ?_, ?_⟩
    · have hh := Finset.card_insert_le θ C
      dsimp [D]
      omega
    · intro hgood
      have hh := ((feasible_iff_pointwise D U L r k).mp hgood).2 θ
        (by simp [D])
      rw [hsame] at hh
      exact hcost hh
  · exact urgent_obstruction B U L r k (by omega)

/-- Checking all subfamilies through size `k+1` is sufficient and necessary. -/
theorem feasible_iff_small_subfamilies (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) :
    Feasible B U L r k ↔ ∀ C ⊆ B, C.card ≤ k + 1 → Feasible C U L r k := by
  constructor
  · intro h C hCB _
    exact feasible_mono_worlds U L r k hCB h
  · intro h
    by_contra hn
    obtain ⟨C, hCB, hc, hbad⟩ := small_obstruction B U L r k hn
    exact hbad (h C hCB hc)

omit [DecidableEq Θ] in
/-- A reserve unavoidable after the largest mandatory union is also
unavoidable in every smaller information set. -/
theorem reserve_lower_subfamily {B C : Finset Θ} (U L : Θ → Finset α)
    (r : Θ → ℕ) (d : ℕ) (hCB : C ⊆ B)
    (hd : ∀ θ ∈ B, d ≤ min (r θ) (L θ \ mandatory B U).card) :
    ∀ θ ∈ C, d ≤ min (r θ) (L θ \ mandatory C U).card := by
  intro θ hθ
  have hm := mandatory_mono U hCB
  have hs : L θ \ mandatory B U ⊆ L θ \ mandatory C U := by
    intro x hx
    obtain ⟨hxL, hxn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxL, fun hxc => hxn (hm hxc)⟩
  have hc := Finset.card_le_card hs
  have hlow := hd θ (hCB hθ)
  omega

omit [DecidableEq Θ] in
theorem feasible_reserve_lower {B C : Finset Θ} (U L : Θ → Finset α)
    (r : Θ → ℕ) (k d : ℕ) (hCB : C ⊆ B) (hne : C.Nonempty)
    (hd : ∀ θ ∈ B, d ≤ min (r θ) (L θ \ mandatory B U).card)
    (hf : Feasible C U L r k) : (mandatory C U).card + d ≤ k := by
  obtain ⟨θ, hθ⟩ := hne
  have hl := reserve_lower_subfamily U L r d hCB hd θ hθ
  have hc := ((feasible_iff_pointwise C U L r k).mp hf).2 θ hθ
  unfold cost at hc
  omega

/-- A common unavoidable late reserve reduces the obstruction size to
`k-d+1` (natural subtraction, hence one world suffices if `d>k`). -/
theorem reserve_obstruction (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k d : ℕ)
    (hd : ∀ θ ∈ B, d ≤ min (r θ) (L θ \ mandatory B U).card)
    (hbad : ¬ Feasible B U L r k) :
    ∃ C ⊆ B, C.card ≤ k - d + 1 ∧ ¬ Feasible C U L r k := by
  classical
  by_cases hdk : d ≤ k
  · by_cases hc : (mandatory B U).card + d ≤ k
    · have hm : (mandatory B U).card ≤ k := by omega
      have hn : ¬ ∀ θ ∈ B, cost (L θ) (mandatory B U) (r θ) ≤ k := by
        intro h
        exact hbad ((feasible_iff_pointwise B U L r k).mpr ⟨hm, h⟩)
      obtain ⟨θ, hθ⟩ := Classical.not_forall.mp hn
      have hθB : θ ∈ B := by
        by_contra h
        exact hθ (fun ht => False.elim (h ht))
      have hcost : ¬ cost (L θ) (mandatory B U) (r θ) ≤ k := by
        intro h
        exact hθ (fun _ => h)
      obtain ⟨C, hCB, hCcard, hcover⟩ :=
        ResourceWitness.cover_by_small_subfamily B U (mandatory B U) (Finset.Subset.refl _)
      let D := insert θ C
      have hDB : D ⊆ B := Finset.insert_subset hθB hCB
      have hCD : C ⊆ D := Finset.subset_insert _ _
      have hsame : mandatory D U = mandatory B U := by
        apply Finset.Subset.antisymm (mandatory_mono U hDB)
        exact Finset.Subset.trans hcover (mandatory_mono U hCD)
      refine ⟨D, hDB, ?_, ?_⟩
      · have hh := Finset.card_insert_le θ C
        dsimp [D]
        omega
      · intro hgood
        have hh := ((feasible_iff_pointwise D U L r k).mp hgood).2 θ
          (by simp [D])
        rw [hsame] at hh
        exact hcost hh
    · obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (by omega :
        k - d + 1 ≤ (mandatory B U).card)
      obtain ⟨C, hCB, hCcard, hcover⟩ :=
        ResourceWitness.cover_by_small_subfamily B U S hS
      have hne : C.Nonempty := by
        by_contra hn
        have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        have hh : S.card ≤ 0 := by
          simpa only [he, Finset.biUnion_empty, Finset.card_empty] using
            Finset.card_le_card hcover
        omega
      refine ⟨C, hCB, by omega, ?_⟩
      intro hf
      have hbound := feasible_reserve_lower U L r k d hCB hne hd hf
      have hcard := Finset.card_le_card hcover
      change S.card ≤ (mandatory C U).card at hcard
      omega
  · have hne : B.Nonempty := by
      by_contra hn
      have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst B
      apply hbad
      exact ⟨∅, by simp [Safe]⟩
    obtain ⟨θ, hθ⟩ := hne
    have hCB : ({θ} : Finset Θ) ⊆ B := by simpa using hθ
    refine ⟨{θ}, hCB, by simp, ?_⟩
    intro hf
    have hbound := feasible_reserve_lower U L r k d hCB (by simp) hd hf
    omega

theorem feasible_iff_reserve_subfamilies (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k d : ℕ)
    (hd : ∀ θ ∈ B, d ≤ min (r θ) (L θ \ mandatory B U).card) :
    Feasible B U L r k ↔
      ∀ C ⊆ B, C.card ≤ k - d + 1 → Feasible C U L r k := by
  constructor
  · intro h C hCB _
    exact feasible_mono_worlds U L r k hCB h
  · intro h
    by_contra hn
    obtain ⟨C, hCB, hc, hbad⟩ := reserve_obstruction B U L r k d hd hn
    exact hbad (h C hCB hc)

/-- A family of singleton urgent targets requires exactly its cardinality. -/
theorem singleton_urgent_iff (B : Finset Θ) (k : ℕ) :
    Feasible B (fun θ => ({θ} : Finset Θ)) (fun _ => ∅) (fun _ => 0) k ↔
      B.card ≤ k := by
  rw [feasible_iff_pointwise]
  simp [mandatory, cost]
  intro h θ _
  exact h

/-- The `k+1` obstruction bound cannot be reduced, for any natural budget. -/
theorem sharp_obstruction (k : ℕ) :
    let B := Finset.range (k + 1)
    ¬ Feasible B (fun i => ({i} : Finset ℕ)) (fun _ => ∅) (fun _ => 0) k ∧
      ∀ C ⊆ B, C.card ≤ k →
        Feasible C (fun i => ({i} : Finset ℕ)) (fun _ => ∅) (fun _ => 0) k := by
  simp only [singleton_urgent_iff, Finset.card_range]
  exact ⟨by omega, fun _ _ hc => hc⟩

end ResourceObstruction

#print axioms ResourceObstruction.small_obstruction
#print axioms ResourceObstruction.feasible_iff_small_subfamilies
#print axioms ResourceObstruction.sharp_obstruction
#print axioms ResourceObstruction.reserve_obstruction
#print axioms ResourceObstruction.feasible_iff_reserve_subfamilies
