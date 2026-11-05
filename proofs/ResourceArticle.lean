import ResourceObstruction
import ResourceExamples

/-! Minimum-budget semantics and the sharp singleton reserve construction. -/

namespace ResourceArticle

open ReserveThreshold

variable {α Θ : Type*} [DecidableEq α]

/-- The threshold is feasible and is no larger than any feasible budget. -/
theorem threshold_is_minimum (B : Finset Θ) (U L : Θ → Finset α)
    (r : Θ → ℕ) :
    Feasible B U L r (threshold B U L r) ∧
      ∀ k, Feasible B U L r k → threshold B U L r ≤ k := by
  exact ⟨(feasible_iff_threshold B U L r _).mpr le_rfl,
    fun k hk => (feasible_iff_threshold B U L r k).mp hk⟩

/-- A single state attains the bound when the late reserve exceeds the budget. -/
theorem late_singleton_sharp (k d : ℕ) (hkd : k < d) :
    (∀ θ ∈ ({0} : Finset ℕ),
      d ≤ min d (Finset.range d \ mandatory ({0} : Finset ℕ) (fun _ => ∅)).card) ∧
    ¬ Feasible ({0} : Finset ℕ) (fun _ => ∅) (fun _ => Finset.range d)
        (fun _ => d) k ∧
    (∀ C ⊆ ({0} : Finset ℕ), C ≠ {0} →
      Feasible C (fun _ => ∅) (fun _ => Finset.range d) (fun _ => d) k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ
    simp [mandatory]
  · rw [feasible_iff_threshold]
    simpa [threshold, mandatory] using Nat.not_le.mpr hkd
  · intro C hC hne
    have he : C = ∅ := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hx0 : x = 0 := by simpa using hC hx
        subst x
        exact False.elim (hne (Finset.Subset.antisymm hC (by simpa using hx)))
      · exact Finset.empty_subset C
    simp [he, feasible_iff_threshold, threshold, mandatory]

end ResourceArticle

#print axioms ResourceArticle.threshold_is_minimum
#print axioms ResourceArticle.late_singleton_sharp
