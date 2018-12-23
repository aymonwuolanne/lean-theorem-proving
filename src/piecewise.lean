import analysis.topology.continuity
import analysis.topology.topological_structures
import analysis.real
import data.set.basic

noncomputable theory

open set 

variables (a : ℝ) (f g : ℝ → ℝ)

def pw : ℝ → ℝ := λ x, if x ≤ a then f x else g x

lemma continuous_pw : continuous f → continuous g → f a = g a → continuous (pw a f g) := 
λ cf cg h, 
  have h₁ : frontier {x | x ≤ a} ⊆ {x | x = a},
    from frontier_le_subset_eq continuous_id continuous_const,
  have hp : ∀ x ∈ frontier {x | x ≤ a}, f x = g x, 
    from λ (x : ℝ) hx, symm (h₁ hx) ▸ h,
  continuous_if hp cf cg
