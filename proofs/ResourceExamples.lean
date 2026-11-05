import ReserveThreshold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Range

/-!
Sharp qualitative boundaries: resource requirements need not have diminishing
returns or LP-type locality. If one action may remove many targets, a budget
of one can have arbitrarily large minimal infeasible families.
-/

namespace ResourceExamples

open ReserveThreshold

def urgent (w : ℕ) : Finset ℕ :=
  if w = 0 then {0} else if w = 1 then {1} else ∅

def late (w : ℕ) : Finset ℕ :=
  if w = 0 then {1} else if w = 2 then {2} else ∅

def quota (w : ℕ) : ℕ := if w = 1 then 0 else 1

def need (B : Finset ℕ) : ℕ := threshold B urgent late quota

/-- Three worlds exhibit a genuine higher-order resource obstruction. -/
theorem three_world_values :
    need {0} = 2 ∧ need {0, 1} = 2 ∧ need {0, 2} = 2 ∧
    need {1, 2} = 2 ∧ need {0, 1, 2} = 3 := by decide

/-- Every pair fits two units, but their union does not. -/
theorem pairs_do_not_suffice :
    Feasible {0, 1} urgent late quota 2 ∧
    Feasible {0, 2} urgent late quota 2 ∧
    Feasible {1, 2} urgent late quota 2 ∧
    ¬ Feasible {0, 1, 2} urgent late quota 2 := by
  simp only [feasible_iff_threshold]
  decide

/-- An additional possible world can cost more in a larger information set:
the standard diminishing-returns inequality for submodularity fails. -/
theorem increasing_marginal_cost :
    need {0, 2} - need {0} < need {0, 1, 2} - need {0, 1} := by decide

/-- Equal values of nested families do not imply equal future violations:
the standard LP-type locality implication fails for this objective. -/
theorem locality_failure :
    ({0} : Finset ℕ) ⊆ {0, 1} ∧
    need {0} = need {0, 1} ∧
    need {0, 2} = need {0} ∧
    need {0, 1} < need {0, 1, 2} := by decide

def reserveUrgent (d w : ℕ) : Finset ℕ := {d + w}
def reserveLate (d : ℕ) (_ : ℕ) : Finset ℕ := Finset.range d

theorem reserve_pool_unchanged (d : ℕ) (B : Finset ℕ) :
    Finset.range d \ mandatory B (reserveUrgent d) = Finset.range d := by
  have hm : mandatory B (reserveUrgent d) = B.image (fun w => d + w) := by
    change B.biUnion (fun w => {d + w}) = B.image (fun w => d + w)
    exact Finset.biUnion_singleton
  rw [hm]
  ext x
  constructor
  · intro hx
    exact (Finset.mem_sdiff.mp hx).1
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
    intro hy
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hy
    have hxd := Finset.mem_range.mp hx
    omega

theorem reserve_example_threshold (d : ℕ) (B : Finset ℕ) (hB : B.Nonempty) :
    threshold B (reserveUrgent d) (reserveLate d) (fun _ => d) = B.card + d := by
  have hm : mandatory B (reserveUrgent d) = B.image (fun w => d + w) := by
    change B.biUnion (fun w => {d + w}) = B.image (fun w => d + w)
    exact Finset.biUnion_singleton
  have hc : (mandatory B (reserveUrgent d)).card = B.card := by
    rw [hm]
    exact Finset.card_image_of_injective B (fun _ _ h => Nat.add_left_cancel h)
  unfold threshold reserveLate
  rw [hc, reserve_pool_unchanged]
  simp only [Finset.card_range, Nat.min_self]
  rw [Finset.sup_const hB]

/-- The reserve-sensitive k-d+1 bound is attained for every d ≤ k. -/
theorem reserve_bound_sharp (k d : ℕ) (hd : d ≤ k) :
    ¬ Feasible (Finset.range (k - d + 1)) (reserveUrgent d) (reserveLate d)
      (fun _ => d) k ∧
    (∀ C : Finset ℕ, C.card ≤ k - d →
      Feasible C (reserveUrgent d) (reserveLate d) (fun _ => d) k) := by
  constructor
  · rw [feasible_iff_threshold,
      reserve_example_threshold d _ (by exact ⟨0, by simp⟩), Finset.card_range]
    omega
  · intro C hC
    rw [feasible_iff_threshold]
    by_cases hn : C.Nonempty
    · rw [reserve_example_threshold d C hn]
      omega
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he, threshold, mandatory]

/-- In the contrasting area-removal model, action j removes every target
except j. One action protects exactly those families that omit some world. -/
def AreaFeasible {W : Type*} (B : Finset W) : Prop :=
  ∃ j : W, ∀ w ∈ B, w ≠ j

theorem area_feasible_iff {W : Type*} [Fintype W] [DecidableEq W]
    (B : Finset W) : AreaFeasible B ↔ B ≠ Finset.univ := by
  classical
  constructor
  · rintro ⟨j, hj⟩ hB
    exact hj j (by simp [hB]) rfl
  · intro hB
    have hx : ∃ j : W, j ∉ B := by
      by_contra hn
      have hall : ∀ j : W, j ∈ B := by
        intro j
        by_contra hj
        exact hn ⟨j, hj⟩
      apply hB
      ext j
      simp [hall j]
    obtain ⟨j, hj⟩ := hx
    refine ⟨j, ?_⟩
    intro w hw heq
    exact hj (heq ▸ hw)

/-- For any positive family size, a single area-removal action has a minimal
infeasible family of exactly that size. Hence no bound depends on budget alone. -/
theorem unbounded_area_obstruction (n : ℕ) :
    ¬ AreaFeasible (Finset.univ : Finset (Fin (n + 1))) ∧
    (∀ C : Finset (Fin (n + 1)), C ≠ Finset.univ → AreaFeasible C) ∧
    (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [area_feasible_iff]
    exact not_not.mpr rfl
  · intro C hC
    exact (area_feasible_iff C).mpr hC
  · simp

end ResourceExamples

#print axioms ResourceExamples.three_world_values
#print axioms ResourceExamples.pairs_do_not_suffice
#print axioms ResourceExamples.increasing_marginal_cost
#print axioms ResourceExamples.locality_failure
#print axioms ResourceExamples.reserve_pool_unchanged
#print axioms ResourceExamples.reserve_bound_sharp
#print axioms ResourceExamples.unbounded_area_obstruction
