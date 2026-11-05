import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# Exact reserve threshold for a two-stage removal game

The common early set must contain every possible urgent target. After the
hidden world is revealed, the adversary can request at most `r` distinct
surviving late targets. Each early or late removal costs one unit.
The game quantifies all allowed late target sets; the closed formula is proved.
-/

namespace ReserveThreshold

variable {α Θ : Type*} [DecidableEq α]

def cost (L E : Finset α) (r : ℕ) : ℕ :=
  E.card + min r (L \ E).card

def mandatory (B : Finset Θ) (U : Θ → Finset α) : Finset α := B.biUnion U

/-- Operational resource condition: every legal distinct-target late attack
can be answered using the units left after the common early removals. -/
def Safe (B : Finset Θ) (U L : Θ → Finset α) (r : Θ → ℕ)
    (k : ℕ) (E : Finset α) : Prop :=
  E.card ≤ k ∧ ∀ θ ∈ B, U θ ⊆ E ∧
    ∀ D : Finset α, D ⊆ L θ \ E → D.card ≤ r θ → E.card + D.card ≤ k

def Feasible (B : Finset Θ) (U L : Θ → Finset α) (r : Θ → ℕ) (k : ℕ) : Prop :=
  ∃ E : Finset α, Safe B U L r k E

theorem late_budget_iff (L E : Finset α) (r k : ℕ) :
    (∀ D : Finset α, D ⊆ L \ E → D.card ≤ r → E.card + D.card ≤ k) ↔
      cost L E r ≤ k := by
  constructor
  · intro h
    obtain ⟨D, hD, hcard⟩ := Finset.exists_subset_card_eq
      (Nat.min_le_right r (L \ E).card)
    have hd : D.card ≤ r := by rw [hcard]; exact Nat.min_le_left _ _
    simpa [cost, hcard] using h D hD hd
  · intro h D hD hr
    have hc := Finset.card_le_card hD
    unfold cost at h
    omega

theorem cost_eq_min (L E : Finset α) (r : ℕ) :
    cost L E r = min (E.card + r) (L ∪ E).card := by
  have hc := Finset.card_sdiff_add_card L E
  unfold cost
  omega

/-- An extra early removal saves at most its own one-unit cost later. -/
theorem cost_mono (L : Finset α) (r : ℕ) {E F : Finset α}
    (hEF : E ⊆ F) : cost L E r ≤ cost L F r := by
  rw [cost_eq_min, cost_eq_min]
  have he := Finset.card_le_card hEF
  have hu := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl L) hEF)
  omega

theorem mandatory_subset_iff (B : Finset Θ) (U : Θ → Finset α) (E : Finset α) :
    mandatory B U ⊆ E ↔ ∀ θ ∈ B, U θ ⊆ E := Finset.biUnion_subset

/-- Every feasible plan can be replaced by the union of the mandatory targets. -/
theorem mandatory_safe_of_safe (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) {E : Finset α} (h : Safe B U L r k E) :
    Safe B U L r k (mandatory B U) := by
  have hm : mandatory B U ⊆ E := (mandatory_subset_iff B U E).mpr
    (fun θ hθ => (h.2 θ hθ).1)
  refine ⟨le_trans (Finset.card_le_card hm) h.1, ?_⟩
  intro θ hθ
  refine ⟨Finset.subset_biUnion_of_mem U hθ, ?_⟩
  apply (late_budget_iff _ _ _ _).mpr
  exact le_trans (cost_mono (L θ) (r θ) hm)
    ((late_budget_iff _ _ _ _).mp (h.2 θ hθ).2)

theorem feasible_iff_mandatory_safe (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) :
    Feasible B U L r k ↔ Safe B U L r k (mandatory B U) := by
  constructor
  · rintro ⟨E, h⟩
    exact mandatory_safe_of_safe B U L r k h
  · intro h
    exact ⟨mandatory B U, h⟩

theorem feasible_iff_pointwise (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) :
    Feasible B U L r k ↔ (mandatory B U).card ≤ k ∧
      ∀ θ ∈ B, cost (L θ) (mandatory B U) (r θ) ≤ k := by
  rw [feasible_iff_mandatory_safe]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, fun θ hθ => (late_budget_iff _ _ _ _).mp (h θ hθ).2⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, fun θ hθ => ⟨Finset.subset_biUnion_of_mem U hθ,
      (late_budget_iff _ _ _ _).mpr (h θ hθ)⟩⟩

def threshold (B : Finset Θ) (U L : Θ → Finset α) (r : Θ → ℕ) : ℕ :=
  (mandatory B U).card + B.sup (fun θ => min (r θ) (L θ \ mandatory B U).card)

/-- Closed-form minimum budget, including the empty information set. -/
theorem feasible_iff_threshold (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) :
    Feasible B U L r k ↔ threshold B U L r ≤ k := by
  rw [feasible_iff_pointwise]
  unfold threshold
  constructor
  · rintro ⟨hm, h⟩
    have hs : B.sup (fun θ => min (r θ) (L θ \ mandatory B U).card) ≤
        k - (mandatory B U).card := by
      apply Finset.sup_le
      intro θ hθ
      have hc := h θ hθ
      unfold cost at hc
      omega
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    intro θ hθ
    have hs : min (r θ) (L θ \ mandatory B U).card ≤
        B.sup (fun φ => min (r φ) (L φ \ mandatory B U).card) :=
      Finset.le_sup (f := fun φ => min (r φ) (L φ \ mandatory B U).card) hθ
    unfold cost
    omega

theorem feasible_mono_worlds {B C : Finset Θ} (U L : Θ → Finset α)
    (r : Θ → ℕ) (k : ℕ) (hCB : C ⊆ B) :
    Feasible B U L r k → Feasible C U L r k := by
  rintro ⟨E, he, h⟩
  exact ⟨E, he, fun θ hθ => h θ (hCB hθ)⟩

/-- Shrinking the information set cannot increase the exact resource demand. -/
theorem threshold_mono_worlds {B C : Finset Θ} (U L : Θ → Finset α)
    (r : Θ → ℕ) (hCB : C ⊆ B) : threshold C U L r ≤ threshold B U L r := by
  apply (feasible_iff_threshold C U L r (threshold B U L r)).mp
  apply feasible_mono_worlds U L r (threshold B U L r) hCB
  exact (feasible_iff_threshold B U L r (threshold B U L r)).mpr le_rfl

end ReserveThreshold

#print axioms ReserveThreshold.late_budget_iff
#print axioms ReserveThreshold.cost_mono
#print axioms ReserveThreshold.mandatory_safe_of_safe
#print axioms ReserveThreshold.feasible_iff_threshold
#print axioms ReserveThreshold.feasible_mono_worlds
#print axioms ReserveThreshold.threshold_mono_worlds
