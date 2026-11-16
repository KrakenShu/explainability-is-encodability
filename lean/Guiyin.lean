import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped BigOperators

namespace Guiyin

structure LayerProjection (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  P : ℕ → (H →L[ℝ] H)
  idempotent : ∀ k, (P k).comp (P k) = P k
  nested : ∀ k, (P (k+1)).comp (P k) = P (k+1)
  eventually_zero : ∃ m, ∀ k > m, P k = 0
  is_orthogonal : ∀ k, IsSelfAdjoint (P k)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma comp_comp_eq (LP : LayerProjection H) {j k : ℕ} (h : k ≤ j) :
    (LP.P j).comp (LP.P k) = LP.P j := by
  induction h with
  | refl => exact LP.idempotent k
  | @step m h ih =>
    calc (LP.P (m+1)).comp (LP.P k)
        = ((LP.P (m+1)).comp (LP.P m)).comp (LP.P k) := by
            exact congrArg (fun f => f.comp (LP.P k)) (LP.nested m).symm
      _ = (LP.P (m+1)).comp ((LP.P m).comp (LP.P k)) := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (LP.P (m+1)).comp (LP.P m) := by rw [ih]
      _ = LP.P (m+1) := by rw [LP.nested m]

lemma comp_comp_eq_rev (LP : LayerProjection H) {j k : ℕ} (h : k ≤ j) :
    (LP.P k).comp (LP.P j) = LP.P j := by
  have h1 : (LP.P j).comp (LP.P k) = LP.P j := Guiyin.comp_comp_eq LP h
  have h2 : ContinuousLinearMap.adjoint ((LP.P j).comp (LP.P k)) =
            ContinuousLinearMap.adjoint (LP.P j) := by rw [h1]
  rw [ContinuousLinearMap.adjoint_comp] at h2
  have hself_j : ContinuousLinearMap.adjoint (LP.P j) = LP.P j := LP.is_orthogonal j
  have hself_k : ContinuousLinearMap.adjoint (LP.P k) = LP.P k := LP.is_orthogonal k
  simpa [hself_j, hself_k] using h2

def layerEnergy (LP : LayerProjection H) (v : H) (j : ℕ) : ℝ :=
  ‖LP.P j v‖^2 - ‖LP.P (j+1) v‖^2

def collapse (LP : LayerProjection H) (k : ℕ) (v : H) : H := LP.P k v

theorem arrow_of_time (LP : LayerProjection H) (v : H) (k : ℕ) :
    ‖LP.P 0 v‖^2 - ‖LP.P 0 (collapse LP k v)‖^2
      = ∑ j ∈ Finset.range k, layerEnergy LP v j := by
  simp only [collapse]
  have hB : ∀ n, LP.P 0 (LP.P n v) = LP.P n v := by
    intro n
    have hcomp : (LP.P 0).comp (LP.P n) = LP.P n :=
      Guiyin.comp_comp_eq_rev LP (Nat.zero_le n)
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun φ => φ v) hcomp
  rw [hB k]
  unfold layerEnergy
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    ring

theorem ultimate_collapse (LP : LayerProjection H) (v : H) :
    ∃ k, collapse LP k v = 0 := by
  rcases LP.eventually_zero with ⟨m, hm⟩
  exact ⟨m + 1, by simp [collapse, hm (m + 1) (Nat.lt_succ_self m)]⟩

theorem collapse_not_surjective (LP : LayerProjection H) (v₀ : H) (hv₀ : v₀ ≠ 0) :
    ∃ k, ¬ Function.Surjective (collapse LP k) := by
  rcases LP.eventually_zero with ⟨m, hm⟩
  refine ⟨m + 1, ?_⟩
  have h0 : LP.P (m + 1) = 0 := hm (m + 1) (Nat.lt_succ_self m)
  intro hsurj
  obtain ⟨w, hw⟩ := hsurj v₀
  simp [collapse, h0] at hw
  exact hv₀ hw.symm

end Guiyin