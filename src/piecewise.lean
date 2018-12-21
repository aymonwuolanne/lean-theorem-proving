import analysis.topology.continuity
import analysis.real

noncomputable theory

variables (a : ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ)

def pw : ℝ → ℝ := λ x, if x ≤ a then f x else g x

lemma continuous_pw : continuous f → continuous g → f a = g a → continuous (pw a f g) := 
begin 
  intros cf cg h,
  rw [pw],
  have ho : - {x | x ≤ a} = {x | x > a}, 
    from sorry,  
  have ho₁ : ∀x∈{x | x > a}, ∃ε>0, ball x ε ⊆ {x | x > a}, 
    intros,
    use ((x-a)/2), 
    

  -- have ho₁ : is_open {x | x > a}, 
  have h : is_closed {x | x ≤ a}, 
    from sorry, 
  have h₁ : closure  {x | x ≤ a} = {x | x ≤ a}, 
    from closure_eq_of_is_closed h,
  have h₂ : interior {x | x ≤ a} = {x | x < a},
  have h₃ : frontier {x | x ≤ a} = {x | x = a},
  have hp : ∀ x ∈ frontier {x | x ≤ a}, f x = g x, 
  repeat {sorry} 
end
-- subset_sInter, and sInter_subset_of_mem should be useful
-- is_open_metric
#check is_open_metric