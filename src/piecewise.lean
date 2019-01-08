import analysis.topology.continuity
import analysis.topology.topological_structures
import analysis.real

noncomputable theory
universe u
variables {α : Type u} [topological_space α] [decidable_linear_order α] [ordered_topology α]
variables {β : Type u} [topological_space β] 
variables (a : α) (f g : α → β)

def pw : α → β := λ x, if x ≤ a then f x else g x

theorem continuous_pw : continuous f → continuous g → f a = g a → continuous (pw a f g) := 
λ cf cg h, 
  have h₁ : frontier {x | x ≤ a} ⊆ {x | x = a},
    from frontier_le_subset_eq continuous_id continuous_const,
  have hp : ∀ x ∈ frontier {x | x ≤ a}, f x = g x, 
    from λ x hx, symm (h₁ hx) ▸ h,
  continuous_if hp cf cg
